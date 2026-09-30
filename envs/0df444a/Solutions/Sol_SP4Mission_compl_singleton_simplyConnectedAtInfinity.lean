-- Prove2me | solution 1 for SP4Mission.compl_singleton_simplyConnectedAtInfinity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T05:35:32.448563+00:00
-- url     : https://prove2.me/submissions/4e3193b0-dae9-42f2-b036-ce902fd9632e

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4Ends
import Theorems.Thm_SP4Mission_sphere_simplyConnected
import Theorems.Thm_SP4Mission_nonempty_homotopyEquiv_punctured_ball_sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission Set

/-!
The complement of a point `p` in a compact `n`-manifold `M` (`n ≥ 3`) is simply connected at
infinity. Given a compact `K ⊆ M ∖ {p}`, choose a coordinate ball `B` around `p` (in the chart
`e` at `p`) missing `K`, and let `L := M ∖ B` — compact, and containing `K`. A loop in
`(M ∖ {p}) ∖ L = B ∖ {p}` is carried by `e` into the punctured Euclidean ball
`e(B) ∖ {e p}`, which is simply connected because it is homotopy equivalent to the unit sphere
`S^{n-1}` (`nonempty_homotopyEquiv_punctured_ball_sphere`) and `S^{n-1}` is simply connected for
`n ≥ 3` (`sphere_simplyConnected`); the contraction is carried back by `e.symm` into
`B ∖ {p} ⊆ (M ∖ {p}) ∖ K`.
-/

/-- Casting a mapped path along a pointwise equality of the maps. -/
private theorem Path.map_cast_of_eqOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (γ : Path x y) {f g : X → Y} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, f (γ t) = g (γ t)) (hx : g x = f x) (hy : g y = f y) :
    (γ.map hf).cast hx hy = γ.map hg := by
  ext t
  simp [Path.cast, h]

theorem solution
    (n : ℕ) (hn : 3 ≤ n) (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) :
    SP4Ends.SimplyConnectedAtInfinity {x : M // x ≠ p} := by
  intro K hK
  set e := chartAt (EuclideanSpace ℝ (Fin n)) p with he
  have hp : p ∈ e.source := mem_chart_source _ p
  -- The image of `K` in `M`: compact, hence closed, and missing `p`.
  set K' : Set M := Subtype.val '' K with hK'
  have hK'c : IsCompact K' := hK.image continuous_subtype_val
  have hpK' : p ∉ K' := by
    rintro ⟨⟨x, hx⟩, -, hxp⟩
    exact hx hxp
  -- A coordinate ball around `p` missing `K'`.
  have hU : IsOpen (e.target ∩ e.symm ⁻¹' K'ᶜ) :=
    e.isOpen_inter_preimage_symm hK'c.isClosed.isOpen_compl
  have hepU : e p ∈ e.target ∩ e.symm ⁻¹' K'ᶜ := by
    refine ⟨e.map_source hp, ?_⟩
    simp only [mem_preimage, mem_compl_iff]
    rw [e.left_inv hp]
    exact hpK'
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU (e p) hepU
  have hball_target : Metric.ball (e p) r ⊆ e.target := fun y hy => (hball hy).1
  set B : Set M := e.source ∩ e ⁻¹' Metric.ball (e p) r with hB
  have hBopen : IsOpen B := e.isOpen_inter_preimage Metric.isOpen_ball
  have hpB : p ∈ B := ⟨hp, Metric.mem_ball_self hr⟩
  have hBK' : ∀ x ∈ B, x ∉ K' := by
    rintro x ⟨hxs, hxb⟩ hxK
    have h := (hball hxb).2
    simp only [mem_preimage, mem_compl_iff] at h
    rw [e.left_inv hxs] at h
    exact h hxK
  -- The compact set `L`: everything outside the coordinate ball.
  refine ⟨{x | (x : M) ∉ B}, ?_, ?_, ?_⟩
  · rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' {x : {x : M // x ≠ p} | (x : M) ∉ B} = Bᶜ := by
      ext y
      constructor
      · rintro ⟨⟨x, hx⟩, hxB, rfl⟩
        exact hxB
      · intro hy
        exact ⟨⟨y, fun h => hy (h ▸ hpB)⟩, hy, rfl⟩
    rw [himg]
    exact hBopen.isClosed_compl.isCompact
  · intro x hx hxB
    exact hBK' x hxB ⟨x, hx, rfl⟩
  · intro x γ
    have hsub : ({x : {x : M // x ≠ p} | (x : M) ∉ B}ᶜ : Set _) ⊆ Kᶜ :=
      Set.compl_subset_compl.mpr (fun x hx hxB => hBK' x hxB ⟨x, hx, rfl⟩)
    -- Points of `Lᶜ` lie in the coordinate ball `B`.
    have hmemB : ∀ z : ({x : {x : M // x ≠ p} | (x : M) ∉ B}ᶜ : Set _), (z : M) ∈ B := by
      intro z
      have hz : (z : {x : M // x ≠ p}) ∈ ({x : {x : M // x ≠ p} | (x : M) ∉ B}ᶜ : Set _) := z.2
      simp only [mem_compl_iff, mem_ofPred_eq, not_not] at hz
      exact hz
    -- The punctured coordinate ball is simply connected: it is homotopy equivalent to the
    -- unit sphere `S^{n-1}`, which is simply connected for `n ≥ 3`.
    have hsph : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      sphere_simplyConnected n hn
    obtain ⟨hequiv⟩ := nonempty_homotopyEquiv_punctured_ball_sphere (e p) hr
    have hPB : SimplyConnectedSpace ↥(Metric.ball (e p) r \ {e p}) :=
      hequiv.simplyConnectedSpace
    -- `ψ`: the chart, from `Lᶜ` into the punctured ball.
    let ψ : ({x : {x : M // x ≠ p} | (x : M) ∉ B}ᶜ : Set _) → ↥(Metric.ball (e p) r \ {e p}) :=
      fun z => ⟨e (z : M), (hmemB z).2,
        fun h => z.1.2 (e.injOn (hmemB z).1 hp (Set.mem_singleton_iff.mp h))⟩
    have hψ : Continuous ψ := by
      apply Continuous.subtype_mk
      exact e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        (fun z => (hmemB z).1)
    -- `χ`: the inverse chart, from the punctured ball into `Kᶜ`.
    have hsymm_ne : ∀ y : ↥(Metric.ball (e p) r \ {e p}),
        e.symm (y : EuclideanSpace ℝ (Fin n)) ≠ p := by
      intro y h
      apply y.2.2
      rw [Set.mem_singleton_iff, ← e.right_inv (hball_target y.2.1), h]
    have hsymm_B : ∀ y : ↥(Metric.ball (e p) r \ {e p}),
        e.symm (y : EuclideanSpace ℝ (Fin n)) ∈ B := by
      intro y
      refine ⟨e.map_target (hball_target y.2.1), ?_⟩
      show e (e.symm (y : EuclideanSpace ℝ (Fin n))) ∈ Metric.ball (e p) r
      rw [e.right_inv (hball_target y.2.1)]
      exact y.2.1
    let χ : ↥(Metric.ball (e p) r \ {e p}) → (Kᶜ : Set {x : M // x ≠ p}) := fun y =>
      ⟨⟨e.symm y, hsymm_ne y⟩, fun hyK => hBK' _ (hsymm_B y) ⟨_, hyK, rfl⟩⟩
    have hχ : Continuous χ := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact e.continuousOn_symm.comp_continuous continuous_subtype_val
        (fun y => hball_target y.2.1)
    -- The composite `χ ∘ ψ` is the inclusion `Lᶜ ⊆ Kᶜ`.
    have hcomp : ∀ z, χ (ψ z) = Set.inclusion hsub z := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      exact e.left_inv (hmemB z).1
    -- Contract the loop in the punctured ball and push the contraction back into `Kᶜ`.
    have h1 : (γ.map hψ).Homotopic (Path.refl (ψ x)) := SimplyConnectedSpace.paths_homotopic _ _
    have h2 := h1.map ⟨χ, hχ⟩
    rw [Path.map_map] at h2
    have h3 := h2.pathCast (hcomp x).symm (hcomp x).symm
    have hL : (γ.map (hχ.comp hψ)).cast (hcomp x).symm (hcomp x).symm =
        γ.map (continuous_inclusion hsub) :=
      Path.map_cast_of_eqOn γ (hχ.comp hψ) (continuous_inclusion hsub) (fun t => hcomp (γ t)) _ _
    have hR : ((Path.refl (ψ x)).map hχ).cast (hcomp x).symm (hcomp x).symm =
        Path.refl (Set.inclusion hsub x) := by
      ext t
      simp [Path.cast, hcomp]
    rw [hL, hR] at h3
    exact h3
