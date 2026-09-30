-- Prove2me | solution 1 for SP4Mission.weaklyContractible_of_homotopyEquiv
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-09T04:05:30.607244+00:00
-- url     : https://prove2.me/submissions/4d300667-7e9a-4034-b6c2-7e5db5e178cf

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open SP4Mission

/-!
# Weak contractibility is invariant under homotopy equivalence

Let `e : X ≃ₕ Y` be a homotopy equivalence with homotopy inverse `g`, and suppose all homotopy
groups of `X` vanish. We show that all homotopy groups of `Y` vanish (Hatcher, §4.1, p. 342).

Mathlib has no induced maps on `HomotopyGroup`, so we argue directly on generalized loops.
Let `φ : (I^n, ∂I^n) → (Y, y)`, `n ≥ 1`. The homotopy `f ∘ g ≃ id` gives a free homotopy from `φ`
to `f ∘ g ∘ φ` whose restriction to `∂I^n` is, at each time, the constant `H(t, y)`; and
`g ∘ φ` is null-homotopic relative to `∂I^n` in `X`, so `f ∘ g ∘ φ` is null-homotopic relative to
`∂I^n` in `Y`. Concatenating, `φ` is *freely* null-homotopic through a homotopy `Φ` that is
constant on `∂I^n` at each time. The key lemma (`homotopic_const_of_free`) turns this into a
null-homotopy relative to the boundary: shrink `Φ_s` into the concentric cube of radius
`1 - s/2` and fill the collar with the trace `γ(t) = Φ(t, ∂I^n)` of the base point (a piecewise
definition glued along the frontier of the inner region), arriving at a map that factors through
the path `γ`, which is then contracted along `γ`. Degree `0` is path connectedness, transported
along `e` directly.
-/


open Set Metric unitInterval Topology Topology.Homotopy

namespace WCTransfer

/-! ### 1. The cube `I^N`: centre, normalized sup-radius, rescaling -/

section Cube

variable {N : Type*} [Fintype N]

/-- The centre `(1/2, …, 1/2)` of the cube. -/
noncomputable def ctr : I^N := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩

/-- Normalized sup-distance to the centre: `r z = max_i |2 z_i - 1| ∈ [0, 1]`; `r z = 1` on the
boundary of the cube. -/
noncomputable def r (z : I^N) : ℝ := 2 * dist z ctr

theorem continuous_r : Continuous (r (N := N)) :=
  continuous_const.mul (continuous_id.dist continuous_const)

theorem r_nonneg (z : I^N) : 0 ≤ r z := mul_nonneg zero_le_two dist_nonneg

theorem coord_le_r (z : I^N) (i : N) : |2 * (z i : ℝ) - 1| ≤ r z := by
  have h := dist_le_pi_dist z ctr i
  rw [Subtype.dist_eq, Real.dist_eq] at h
  have hc : ((ctr i : I) : ℝ) = 1 / 2 := rfl
  rw [hc] at h
  unfold r
  calc |2 * (z i : ℝ) - 1| = 2 * |(z i : ℝ) - 1 / 2| := by
        rw [show (2 : ℝ) * z i - 1 = 2 * (z i - 1 / 2) by ring, abs_mul, abs_two]
    _ ≤ 2 * dist z ctr := by linarith

theorem r_le_one (z : I^N) : r z ≤ 1 := by
  unfold r
  have : dist z ctr ≤ 1 / 2 := by
    rw [dist_pi_le_iff (by norm_num)]
    intro i
    rw [Subtype.dist_eq, Real.dist_eq]
    have hc : ((ctr i : I) : ℝ) = 1 / 2 := rfl
    rw [hc, abs_le]
    constructor <;> linarith [(z i).2.1, (z i).2.2]
  linarith

theorem exists_coord_eq_r [Nonempty N] (z : I^N) : ∃ i, |2 * (z i : ℝ) - 1| = r z := by
  unfold r
  rw [dist_pi_def]
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun b => nndist (z b) (ctr b))
  refine ⟨i, ?_⟩
  rw [hi, coe_nndist, Subtype.dist_eq, Real.dist_eq]
  have hc : ((ctr i : I) : ℝ) = 1 / 2 := rfl
  rw [hc, show (2 : ℝ) * z i - 1 = 2 * (z i - 1 / 2) by ring, abs_mul, abs_two]

theorem r_eq_one_of_mem_boundary {z : I^N} (hz : z ∈ Cube.boundary N) : r z = 1 := by
  obtain ⟨i, hi⟩ := hz
  apply le_antisymm (r_le_one z)
  have h := coord_le_r z i
  rcases hi with h0 | h1
  · rw [h0] at h
    norm_num at h
    exact h
  · rw [h1] at h
    norm_num at h
    exact h

/-- Radius of the inner cube at time `s`: `ρ s = 1 - s/2 ∈ [1/2, 1]`. -/
noncomputable def ρ (s : I) : ℝ := 1 - (s : ℝ) / 2

theorem continuous_ρ : Continuous ρ := by unfold ρ; fun_prop

theorem ρ_pos (s : I) : 0 < ρ s := by unfold ρ; linarith [s.2.2]

theorem ρ_zero : ρ 0 = 1 := by simp [ρ]

theorem ρ_one : ρ 1 = 1 / 2 := by simp [ρ]; norm_num

/-- Rescaling of the inner cube of radius `ρ s` onto the whole cube (clamped outside it). -/
noncomputable def resc (s : I) (z : I^N) : I^N :=
  fun i => projIcc 0 1 zero_le_one (1 / 2 + ((z i : ℝ) - 1 / 2) / ρ s)

theorem continuous_resc : Continuous (fun p : I × I^N => resc p.1 p.2) := by
  refine continuous_pi fun i => continuous_projIcc.comp ?_
  have h1 : Continuous fun p : I × I^N => ((p.2 i : I) : ℝ) - 1 / 2 :=
    (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)).sub continuous_const
  have h2 : Continuous fun p : I × I^N => ρ p.1 := continuous_ρ.comp continuous_fst
  exact continuous_const.add (h1.div h2 fun p => (ρ_pos p.1).ne')

theorem resc_zero (z : I^N) : resc 0 z = z := by
  funext i
  unfold resc
  rw [ρ_zero, div_one, show (1 : ℝ) / 2 + ((z i : I) - 1 / 2) = z i by ring]
  exact projIcc_val zero_le_one (z i)

theorem resc_mem_boundary [Nonempty N] {s : I} {z : I^N} (h : r z = ρ s) :
    resc s z ∈ Cube.boundary N := by
  obtain ⟨i, hi⟩ := exists_coord_eq_r z
  rw [h] at hi
  refine ⟨i, ?_⟩
  have hρ := ρ_pos s
  rcases (abs_eq hρ.le).mp hi with h1 | h1
  · right
    show projIcc 0 1 zero_le_one (1 / 2 + ((z i : ℝ) - 1 / 2) / ρ s) = 1
    have : (1 : ℝ) / 2 + ((z i : ℝ) - 1 / 2) / ρ s = 1 := by
      have : ((z i : ℝ) - 1 / 2) / ρ s = 1 / 2 := by
        rw [div_eq_iff hρ.ne']; linarith
      linarith
    rw [this]
    exact projIcc_right zero_le_one
  · left
    show projIcc 0 1 zero_le_one (1 / 2 + ((z i : ℝ) - 1 / 2) / ρ s) = 0
    have : (1 : ℝ) / 2 + ((z i : ℝ) - 1 / 2) / ρ s = 0 := by
      have : ((z i : ℝ) - 1 / 2) / ρ s = -(1 / 2) := by
        rw [div_eq_iff hρ.ne']; linarith
      linarith
    rw [this]
    exact projIcc_left zero_le_one

end Cube

/-! ### 2. A freely null-homotopic generalized loop is null-homotopic relative to the boundary -/

section Free

variable {N : Type*} [Fintype N] [Nonempty N] {Y : Type*} [TopologicalSpace Y] {y : Y}

/-- **Free ⇒ based.** If `Φ : I × I^N → Y` starts at the generalized loop `φ`, ends at a constant
map, and is constant on the boundary of the cube at each time, then `φ` is null-homotopic relative
to the boundary. -/
theorem homotopic_const_of_free (φ : Ω^ N Y y) (Φ : C(I × I^N, Y))
    (h0 : ∀ z, Φ (0, z) = φ z) (h1 : ∀ z z', Φ (1, z) = Φ (1, z'))
    (hbd : ∀ t, ∀ z ∈ Cube.boundary N, ∀ z' ∈ Cube.boundary N, Φ (t, z) = Φ (t, z')) :
    GenLoop.Homotopic φ GenLoop.const := by
  classical
  -- the trace of the base point
  let z₀ : I^N := fun _ => 0
  have hz₀ : z₀ ∈ Cube.boundary N := ⟨Classical.arbitrary N, Or.inl rfl⟩
  let γ : C(I, Y) := ⟨fun t => Φ (t, z₀), Φ.continuous.comp (Continuous.prodMk_left z₀)⟩
  have hγ0 : γ 0 = y := by
    show Φ (0, z₀) = y
    rw [h0]
    exact GenLoop.boundary φ z₀ hz₀
  have hγbd : ∀ t, ∀ z ∈ Cube.boundary N, Φ (t, z) = γ t := fun t z hz => hbd t z hz z₀ hz₀
  -- collar parameter
  let κ : (N → I) → I := fun z => projIcc 0 1 zero_le_one (2 * (1 - r z))
  have hκc : Continuous κ :=
    continuous_projIcc.comp (continuous_const.mul (continuous_const.sub continuous_r))
  -- Stage 1: shrink `Φ` into the inner cube and fill the collar with the base-point trace.
  let A : Set (I × (N → I)) := {p | r p.2 ≤ ρ p.1}
  let inner : I × (N → I) → Y := fun p => Φ (p.1, resc p.1 p.2)
  let collar : I × (N → I) → Y := fun p => γ (κ p.2)
  have hinner : Continuous inner := Φ.continuous.comp (continuous_fst.prodMk continuous_resc)
  have hcollar : Continuous collar := γ.continuous.comp (hκc.comp continuous_snd)
  have hrc : Continuous fun p : I × I^N => r p.2 := continuous_r.comp continuous_snd
  have hρc : Continuous fun p : I × I^N => ρ p.1 := continuous_ρ.comp continuous_fst
  have hA : IsClosed A := isClosed_le hrc hρc
  have hfront : ∀ p ∈ frontier A, inner p = collar p := by
    intro p hp
    have hp' : r p.2 = ρ p.1 := frontier_le_subset_eq hrc hρc hp
    show Φ (p.1, resc p.1 p.2) = γ (κ p.2)
    rw [hγbd _ _ (resc_mem_boundary hp')]
    congr 1
    show p.1 = projIcc 0 1 zero_le_one (2 * (1 - r p.2))
    rw [hp']
    unfold ρ
    rw [show (2 : ℝ) * (1 - (1 - (p.1 : ℝ) / 2)) = p.1 by ring]
    exact (projIcc_val zero_le_one p.1).symm
  let Ψf : I × (N → I) → Y := A.piecewise inner collar
  have hΨc : Continuous Ψf := by
    apply continuous_piecewise hfront
    · exact hinner.continuousOn
    · exact hcollar.continuousOn
  -- the map at the end of Stage 1
  let K₀f : (N → I) → Y := fun z => γ (projIcc 0 1 zero_le_one (min 1 (2 * (1 - r z))))
  have hK₀c : Continuous K₀f :=
    γ.continuous.comp (continuous_projIcc.comp
      (continuous_const.min (continuous_const.mul (continuous_const.sub continuous_r))))
  let K₀ : C(I^N, Y) := ⟨K₀f, hK₀c⟩
  let Ψ : ContinuousMap.HomotopyRel (φ : C(I^N, Y)) K₀ (Cube.boundary N) :=
    { toFun := Ψf
      continuous_toFun := hΨc
      map_zero_left := by
        intro z
        have hmem : ((0 : I), z) ∈ A := by
          show r z ≤ ρ 0
          rw [ρ_zero]; exact r_le_one z
        show A.piecewise inner collar (0, z) = φ z
        rw [Set.piecewise_eq_of_mem _ _ _ hmem]
        show Φ (0, resc 0 z) = φ z
        rw [resc_zero, h0]
      map_one_left := by
        intro z
        show A.piecewise inner collar (1, z) = K₀f z
        by_cases hmem : ((1 : I), z) ∈ A
        · rw [Set.piecewise_eq_of_mem _ _ _ hmem]
          have hr : r z ≤ 1 / 2 := by
            have : r z ≤ ρ 1 := hmem
            rwa [ρ_one] at this
          show Φ (1, resc 1 z) = γ (projIcc 0 1 zero_le_one (min 1 (2 * (1 - r z))))
          rw [h1 (resc 1 z) z₀]
          show γ 1 = _
          congr 1
          rw [min_eq_left (by linarith)]
          exact (projIcc_right zero_le_one).symm
        · rw [Set.piecewise_eq_of_notMem _ _ _ hmem]
          have hr : 1 / 2 < r z := by
            have : ¬ r z ≤ ρ 1 := hmem
            rw [ρ_one] at this
            exact lt_of_not_ge this
          show γ (projIcc 0 1 zero_le_one (2 * (1 - r z))) =
            γ (projIcc 0 1 zero_le_one (min 1 (2 * (1 - r z))))
          rw [min_eq_right (by linarith)]
      prop' := by
        intro t z hz
        show A.piecewise inner collar (t, z) = φ z
        rw [GenLoop.boundary φ z hz]
        have hr := r_eq_one_of_mem_boundary hz
        by_cases hmem : (t, z) ∈ A
        · rw [Set.piecewise_eq_of_mem _ _ _ hmem]
          have ht : t = 0 := by
            have h1' : (1 : ℝ) ≤ ρ t := hr ▸ hmem
            unfold ρ at h1'
            exact Subtype.ext (by linarith [t.2.1] : (t : ℝ) = 0)
          subst ht
          show Φ (0, resc 0 z) = y
          rw [resc_zero, h0]
          exact GenLoop.boundary φ z hz
        · rw [Set.piecewise_eq_of_notMem _ _ _ hmem]
          show γ (projIcc 0 1 zero_le_one (2 * (1 - r z))) = y
          rw [hr, show (2 : ℝ) * (1 - 1) = 0 by ring, projIcc_left]
          exact hγ0 }
  -- Stage 2: contract the collar map `K₀` along the trace.
  let Kf : I × (N → I) → Y := fun p =>
    γ (projIcc 0 1 zero_le_one ((1 - (p.1 : ℝ)) * min 1 (2 * (1 - r p.2))))
  have hKc : Continuous Kf := by
    refine γ.continuous.comp (continuous_projIcc.comp ?_)
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_const.min (continuous_const.mul (continuous_const.sub hrc)))
  let K : ContinuousMap.HomotopyRel K₀ (ContinuousMap.const (I^N) y) (Cube.boundary N) :=
    { toFun := Kf
      continuous_toFun := hKc
      map_zero_left := by
        intro z
        show γ (projIcc 0 1 zero_le_one ((1 - ((0 : I) : ℝ)) * min 1 (2 * (1 - r z)))) = K₀f z
        show _ = γ (projIcc 0 1 zero_le_one (min 1 (2 * (1 - r z))))
        rw [Set.Icc.coe_zero, sub_zero, one_mul]
      map_one_left := by
        intro z
        show γ (projIcc 0 1 zero_le_one ((1 - ((1 : I) : ℝ)) * min 1 (2 * (1 - r z)))) = y
        rw [Set.Icc.coe_one, sub_self, zero_mul, projIcc_left]
        exact hγ0
      prop' := by
        intro t z hz
        show γ (projIcc 0 1 zero_le_one ((1 - (t : ℝ)) * min 1 (2 * (1 - r z)))) = K₀f z
        show _ = γ (projIcc 0 1 zero_le_one (min 1 (2 * (1 - r z))))
        rw [r_eq_one_of_mem_boundary hz, show (2 : ℝ) * (1 - 1) = 0 by ring, min_eq_right zero_le_one,
          mul_zero] }
  exact ⟨Ψ.trans K⟩

end Free

/-! ### 3. Transfer of weak contractibility along a homotopy equivalence -/

section Transfer

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem pathConnectedSpace_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y)
    [PathConnectedSpace X] : PathConnectedSpace Y := by
  obtain ⟨H⟩ := e.right_inv
  refine ⟨PathConnectedSpace.nonempty.map e.toFun, fun a b => ?_⟩
  have h1 : Joined (e.toFun (e.invFun a)) a := ⟨H.evalAt a⟩
  have h2 : Joined (e.toFun (e.invFun b)) b := ⟨H.evalAt b⟩
  have h3 : Joined (e.toFun (e.invFun a)) (e.toFun (e.invFun b)) :=
    (PathConnectedSpace.joined _ _).map e.toFun.continuous
  exact h1.symm.trans (h3.trans h2)

theorem pathConnectedSpace_of_pi0 {x : X} (h : Subsingleton (π_ 0 X x)) : PathConnectedSpace X := by
  rw [pathConnectedSpace_iff_zerothHomotopy]
  exact ⟨⟨⟦x⟧⟩, (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm.subsingleton⟩

/-- Every generalized loop (of positive dimension) in `Y` is null-homotopic when `Y` is homotopy
equivalent to a space with trivial homotopy groups. -/
theorem genLoop_nullhomotopic (e : ContinuousMap.HomotopyEquiv X Y)
    (hX : ∀ (n : ℕ) (x : X), Subsingleton (π_ n X x)) (m : ℕ) (y : Y)
    (φ : Ω^ (Fin (m + 1)) Y y) : GenLoop.Homotopic φ GenLoop.const := by
  -- `g ∘ φ` as a generalized loop in `X` at `g y`
  let gφ : Ω^ (Fin (m + 1)) X (e.invFun y) :=
    ⟨e.invFun.comp (φ : C(I^(Fin (m + 1)), Y)), fun z hz => by
      show e.invFun (φ z) = e.invFun y
      rw [GenLoop.boundary φ z hz]⟩
  have hsub := hX (m + 1) (e.invFun y)
  have hG : GenLoop.Homotopic gφ GenLoop.const :=
    Quotient.exact (@Subsingleton.elim _ hsub (Quotient.mk _ gφ) (Quotient.mk _ GenLoop.const))
  obtain ⟨G⟩ := hG
  obtain ⟨H⟩ := e.right_inv
  -- the free null-homotopy of `φ`: first `φ ⇝ f ∘ g ∘ φ` via `H`, then `f ∘ (g ∘ φ ⇝ const)`.
  let Φ₁ := H.symm.compContinuousMap (φ : C(I^(Fin (m + 1)), Y))
  let Φ₂ := (ContinuousMap.Homotopy.refl e.toFun).comp G.toHomotopy
  let Φ := Φ₁.trans Φ₂
  apply homotopic_const_of_free φ Φ.toContinuousMap
  · intro z
    show Φ (0, z) = φ z
    rw [Φ.apply_zero]
    rfl
  · intro z z'
    show Φ (1, z) = Φ (1, z')
    rw [Φ.apply_one, Φ.apply_one]
    rfl
  · intro t z hz z' hz'
    show Φ (t, z) = Φ (t, z')
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · show H (σ _, φ z) = H (σ _, φ z')
      rw [GenLoop.boundary φ z hz, GenLoop.boundary φ z' hz']
    · show e.toFun (G (_, z)) = e.toFun (G (_, z'))
      rw [G.eq_fst _ hz, G.eq_fst _ hz']
      show e.toFun (e.invFun (φ z)) = e.toFun (e.invFun (φ z'))
      rw [GenLoop.boundary φ z hz, GenLoop.boundary φ z' hz']

/-- **Weak contractibility is invariant under homotopy equivalence.** -/
theorem weaklyContractible_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y)
    (hX : SP4WeakHomotopy.WeaklyContractible X) : SP4WeakHomotopy.WeaklyContractible Y := by
  obtain ⟨hne, hπ⟩ := hX
  have hpcX : PathConnectedSpace X := pathConnectedSpace_of_pi0 (hπ 0 (Classical.choice hne))
  have hpcY : PathConnectedSpace Y := pathConnectedSpace_of_homotopyEquiv e
  refine ⟨hne.map e.toFun, fun n y => ?_⟩
  cases n with
  | zero => exact (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := y)).subsingleton
  | succ m =>
    refine ⟨fun a b => ?_⟩
    induction a using Quotient.inductionOn with
    | _ φ =>
    induction b using Quotient.inductionOn with
    | _ ψ =>
    exact Quotient.sound
      ((genLoop_nullhomotopic e hπ m y φ).trans (genLoop_nullhomotopic e hπ m y ψ).symm)

end Transfer

end WCTransfer

/-- The target theorem. -/
theorem solution.{u, v}
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (hX : SP4WeakHomotopy.WeaklyContractible X) :
    SP4WeakHomotopy.WeaklyContractible Y :=
  WCTransfer.weaklyContractible_of_homotopyEquiv e hX
