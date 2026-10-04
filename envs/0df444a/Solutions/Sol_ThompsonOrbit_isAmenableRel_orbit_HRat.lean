-- Prove2me | solution 1 for ThompsonOrbit.isAmenableRel_orbit_HRat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T06:28:24.965527+00:00
-- url     : https://prove2.me/submissions/69a022f7-811a-4fdd-856c-976aa7dbecb6

import Definitions.Def_ThompsonAmenability
import Theorems.Thm_Monod_contDiff_and_exists_mulEquiv_HRat_F
import Theorems.Thm_Monod_isAmenableRel_orbit_of_isAmenable
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_exists_mem_F_map_partition
import Theorems.Thm_Garrido_isAmenable_of_isSolvable_of_finiteIndex
import Theorems.Thm_CannonFloydParry_bijOn_dyadic
import Mathlib


section
section
section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-!
# Blueprint: Monod 2023, Theorem 5.1

`H_ℚ(ℤ)` (`Monod.HRat`) is not co-amenable in `H_ℚ(ℚ)` (`HB ratSubring Monod.ratPoints`) nor in
`H^{C¹}_ℚ(ℚ)` (`HC1RatRat`).

Route (Monod 2023, Theorem 4.6, "the same statement holds with Γ∅ replaced throughout by
Thompson's group", and Proposition 4.7):
* Part A — the containments `HRat ≤ HC1RatRat ≤ HB ratSubring ratPoints`.
* Part B — every element of `HB ratSubring ratPoints` agrees with a Möbius map of `SL₂(ℚ)` at each
  irrational point and preserves Lebesgue-null sets.
* Part C — cut-and-paste: one explicit element of `HRat` realises `x ↦ -1/x` on `(1, 2)`; with the
  rational affine maps (in `HC1RatRat`) it realises every `g ∈ SL₂(ℚ)` at every irrational point.
* Part D — relative Zimmer (Monod 2023, Proposition 4.7), for means: if `Γ ≤ Λ` is co-amenable and
  the `Γ`-orbit relation is amenable, then so is any relation `R` that agrees with the `Λ`-orbit
  relation on a conull saturated set.
* Part E — the orbit relation of `HRat` on `P¹` is amenable: via the published conjugacy of `HRat`
  with Thompson's `F` on `(0,1)`, it is the orbit relation of the amenable dyadic affine group.
* Assembly — co-amenability would make the `SL₂(ℚ)` orbit relation amenable, contradicting
  `Monod.not_isAmenableRel_mob` (Carrière–Ghys, the dense subring `ℚ`).
-/
/-- Homeomorphisms of `P¹`. -/
abbrev Hom := OnePoint ℝ ≃ₜ OnePoint ℝ

/-- Homeomorphisms of `P¹` act on `P¹` by evaluation. -/
instance instMulActionHom : MulAction Hom (OnePoint ℝ) where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_def (g : Hom) (x : OnePoint ℝ) : g • x = g x := rfl

/-- `SL₂(ℚ)`, with `ℚ` as the subring `ratSubring` of `ℝ`. -/
abbrev SLQ := Matrix.SpecialLinearGroup (Fin 2) ratSubring

/-- The orbit relation of a group of homeomorphisms of `P¹`. -/
def orbRel (Λ : Subgroup Hom) : Set (OnePoint ℝ × OnePoint ℝ) := {p | ∃ g ∈ Λ, g • p.1 = p.2}

/-- The irrational points of the line, inside `P¹`. -/
def X0 : Set (OnePoint ℝ) := {x | ∃ r : ℝ, Irrational r ∧ x = (r : OnePoint ℝ)}

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
/-!
# Monod 2023, Theorem 5.1 — Part A (and Part E3)

* The containments `HRat ≤ HC1RatRat ≤ HB ratSubring ratPoints`, and `HRat ≤ HB ratSubring ratPoints`.
* `ratSubring` is countable and dense; `volP1` is σ-finite.
* Part E3: amenability of a measured relation passes to a relation that agrees with it on a
  conull set saturated for the new relation.
-/
/-! ## Containments -/
/-- Enlarging the ring does not change the Möbius action. -/
theorem mob_map_inclusion {A B : Subring ℝ} (hle : A ≤ B)
    (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    Monod.mob (Matrix.SpecialLinearGroup.map (Subring.inclusion hle) g) = Monod.mob g := by
  have : Monod.slToGL B (Matrix.SpecialLinearGroup.map (Subring.inclusion hle) g) =
      Monod.slToGL A g := by
    ext i j
    rfl
  funext x
  simp only [Monod.mob, this]

/-- Being piecewise in `SL₂(A)` is monotone in the ring `A`. -/
theorem isPiecewiseProjOn_mono {A B : Subring ℝ} (hle : A ≤ B) {E : Set (OnePoint ℝ)}
    {f : OnePoint ℝ ≃ₜ OnePoint ℝ} (hf : Monod.IsPiecewiseProjOn A E f) :
    Monod.IsPiecewiseProjOn B E f := by
  obtain ⟨S, hSE, hloc⟩ := hf
  refine ⟨S, hSE, fun x hx => ?_⟩
  obtain ⟨g, hg⟩ := hloc x hx
  exact ⟨Matrix.SpecialLinearGroup.map (Subring.inclusion hle) g, by
    rw [mob_map_inclusion]; exact hg⟩

theorem HRat_le_HB : Monod.HRat ≤ HB ratSubring Monod.ratPoints := by
  unfold Monod.HRat Monod.GRat HB
  apply inf_le_inf_right
  apply Subgroup.closure_mono
  rintro f ⟨hG, hf⟩
  exact ⟨hG, isPiecewiseProjOn_mono bot_le hf⟩

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part A: containments and the subring `ℚ` -/
alias HRat_le_HB := ThompsonAmenability.M51.PartA.HRat_le_HB

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
/-! ## The subring `ℚ` -/

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
variable {A : Subring ℝ}
/-!
# Monod 2023, Theorem 5.1 — Part B: elements of `H_ℚ(ℚ)` at irrational points

* `X0ᶜ = {∞} ∪ ℚ` is countable, hence measurable and `volP1`-null.
* A Möbius map with rational entries preserves the irrational points (and so does its inverse).
* Every generator of `H_ℚ(ℚ)` agrees at every point of `P¹` with a Möbius map of `SL₂(ℚ)`: off the
  breakpoints by definition, and at a breakpoint by the identity theorem on an adjacent interval
  free of breakpoints together with continuity. Closure induction then gives
  `exists_mob_of_mem_HB`.
* Möbius maps are smooth off their pole, so they pull null sets back to null sets; an element of
  `H_ℚ(ℚ)` pulls a null set back into `X0ᶜ` union countably many Möbius preimages.

The basic Möbius facts (formulas, group law, continuity, identity theorem) are adapted from
`Solutions/Monod/DynBasic.lean`, `DynGerm.lean`, `RedMob.lean` and `RedNull.lean`.
-/
/-! ### Möbius maps: formulas, group law, continuity -/
/-- real entries -/
noncomputable abbrev ent (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) : ℝ :=
  ((g i j : A) : ℝ)

lemma slToGL_apply (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    (Monod.slToGL A g : GL (Fin 2) ℝ) i j = ent g i j := by
  simp [Monod.slToGL]

lemma det_ent (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun x : A => (x : ℝ)) h
  simpa using this

lemma mob_coe (g : Matrix.SpecialLinearGroup (Fin 2) A) (t : ℝ) :
    Monod.mob g (t : OnePoint ℝ) = if ent g 1 0 * t + ent g 1 1 = 0 then ∞ else
      (((ent g 0 0 * t + ent g 0 1) / (ent g 1 0 * t + ent g 1 1) : ℝ) : OnePoint ℝ) := by
  unfold Monod.mob
  rw [OnePoint.smul_some_eq_ite]
  simp only [slToGL_apply]

lemma mob_infty (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    Monod.mob g ∞ = if ent g 1 0 = 0 then ∞ else ((ent g 0 0 / ent g 1 0 : ℝ) : OnePoint ℝ) := by
  unfold Monod.mob
  rw [OnePoint.smul_infty_eq_ite]
  simp only [slToGL_apply]

lemma mob_mul (g h : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    Monod.mob (g * h) x = Monod.mob g (Monod.mob h x) := by
  unfold Monod.mob
  rw [map_mul, mul_smul]

lemma mob_one (x : OnePoint ℝ) : Monod.mob (1 : Matrix.SpecialLinearGroup (Fin 2) A) x = x := by
  unfold Monod.mob
  rw [map_one, one_smul]

lemma mob_inv_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    Monod.mob g⁻¹ (Monod.mob g x) = x := by
  rw [← mob_mul, inv_mul_cancel, mob_one]

lemma mob_mob_inv (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    Monod.mob g (Monod.mob g⁻¹ x) = x := by
  rw [← mob_mul, mul_inv_cancel, mob_one]

lemma tendsto_coe_cobounded :
    Tendsto (fun x : ℝ => (x : OnePoint ℝ)) (Bornology.cobounded ℝ) (𝓝 ∞) := by
  rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact]
  exact tendsto_coe_infty

lemma tendsto_affine_cobounded {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    Tendsto (fun x : ℝ => c * x + d) (Bornology.cobounded ℝ) (Bornology.cobounded ℝ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h1 := tendsto_norm_cobounded_atTop (E := ℝ)
  have h2 : Tendsto (fun x : ℝ => |c| * ‖x‖ - |d|) (Bornology.cobounded ℝ) atTop := by
    apply tendsto_atTop_add_const_right
    exact h1.const_mul_atTop (abs_pos.2 hc)
  refine tendsto_atTop_mono (fun x => ?_) h2
  simp only [Real.norm_eq_abs]
  have := abs_sub_abs_le_abs_sub (c * x) (-d)
  rw [abs_mul, abs_neg, sub_neg_eq_add] at this
  linarith

lemma frac_eq (g : Matrix.SpecialLinearGroup (Fin 2) A) {x : ℝ} (hc : ent g 1 0 ≠ 0)
    (hx : ent g 1 0 * x + ent g 1 1 ≠ 0) :
    (ent g 0 0 * x + ent g 0 1) / (ent g 1 0 * x + ent g 1 1) =
      ent g 0 0 / ent g 1 0 - (ent g 1 0 * (ent g 1 0 * x + ent g 1 1))⁻¹ := by
  have := det_ent g
  rw [eq_sub_iff_add_eq, div_eq_mul_inv, mul_inv, ← add_mul, ← div_eq_mul_inv]
  rw [div_eq_div_iff hx hc, add_mul, inv_mul_cancel₀ hc]
  linear_combination (-1 : ℝ) * this

lemma continuous_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) : Continuous (Monod.mob g) := by
  have hdet := det_ent g
  rw [OnePoint.continuous_iff]
  constructor
  · rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    by_cases hc : ent g 1 0 = 0
    · have hd : ent g 1 1 ≠ 0 := by
        intro h; rw [h, hc] at hdet; simp at hdet
      rw [mob_infty, if_pos hc]
      have : (fun x : ℝ => Monod.mob g (x : OnePoint ℝ)) =
          fun x : ℝ => (((ent g 0 0 / ent g 1 1) * x + ent g 0 1 / ent g 1 1 : ℝ) :
            OnePoint ℝ) := by
        funext x
        rw [mob_coe, if_neg (by rw [hc]; simpa using hd)]
        congr 1
        rw [hc, zero_mul, zero_add]; field_simp
      rw [this]
      have ha : ent g 0 0 ≠ 0 := by
        intro h; rw [h, hc] at hdet; simp at hdet
      exact tendsto_coe_cobounded.comp (tendsto_affine_cobounded (div_ne_zero ha hd) _)
    · rw [mob_infty, if_neg hc]
      have hev : ∀ᶠ x : ℝ in Bornology.cobounded ℝ, ent g 1 0 * x + ent g 1 1 ≠ 0 := by
        have := (tendsto_affine_cobounded hc (ent g 1 1)).eventually
          (Bornology.eventually_ne_cobounded (0 : ℝ))
        exact this
      have hlim : Tendsto (fun x : ℝ => ((ent g 0 0 / ent g 1 0 -
          (ent g 1 0 * (ent g 1 0 * x + ent g 1 1))⁻¹ : ℝ) : OnePoint ℝ))
          (Bornology.cobounded ℝ) (𝓝 ((ent g 0 0 / ent g 1 0 : ℝ) : OnePoint ℝ)) := by
        apply (continuous_coe.tendsto _).comp
        have h3 : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1))
            (Bornology.cobounded ℝ) (Bornology.cobounded ℝ) := by
          have := tendsto_affine_cobounded (mul_ne_zero hc hc) (ent g 1 0 * ent g 1 1)
          refine this.congr (fun x => ?_)
          ring
        have h4 := (tendsto_inv₀_cobounded.comp h3)
        have := (tendsto_const_nhds (x := ent g 0 0 / ent g 1 0)).sub h4
        simpa using this
      refine hlim.congr' ?_
      filter_upwards [hev] with x hx
      rw [mob_coe, if_neg hx, frac_eq g hc hx]
  · rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : ent g 1 0 * t + ent g 1 1 = 0
    · have hc : ent g 1 0 ≠ 0 := by
        intro h; rw [h, zero_mul, zero_add] at ht; rw [ht, h] at hdet; simp at hdet
      show Tendsto (fun x : ℝ => Monod.mob g (x : OnePoint ℝ)) (𝓝 t)
        (𝓝 (Monod.mob g (t : OnePoint ℝ)))
      rw [mob_coe, if_pos ht, ← nhdsNE_sup_pure t, tendsto_sup]
      constructor
      · have h3 : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1))
            (𝓝[≠] t) (𝓝[≠] 0) := by
          apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
          · have : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1)) (𝓝 t)
                (𝓝 (ent g 1 0 * (ent g 1 0 * t + ent g 1 1))) :=
              ((continuous_const.mul ((continuous_const.mul continuous_id).add
                continuous_const)).tendsto t)
            rw [ht, mul_zero] at this
            exact tendsto_nhdsWithin_of_tendsto_nhds this
          · filter_upwards [self_mem_nhdsWithin] with x hx
            simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
            intro h0
            rcases mul_eq_zero.1 h0 with h | h
            · exact hc h
            · apply hx
              have : ent g 1 0 * (x - t) = 0 := by linarith
              rcases mul_eq_zero.1 this with h' | h'
              · exact absurd h' hc
              · linarith
        have h4 := tendsto_inv₀_nhdsNE_zero.comp h3
        have h5 := (tendsto_const_add_cobounded (ent g 0 0 / ent g 1 0)).comp
          ((tendsto_neg_cobounded).comp h4)
        refine (tendsto_coe_cobounded.comp h5).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_compl_iff, mem_singleton_iff] at hx
        have hx' : ent g 1 0 * x + ent g 1 1 ≠ 0 := by
          intro h0; apply hx
          have : ent g 1 0 * (x - t) = 0 := by linarith
          rcases mul_eq_zero.1 this with h' | h'
          · exact absurd h' hc
          · linarith
        simp only [Function.comp_apply]
        rw [mob_coe, if_neg hx', frac_eq g hc hx', sub_eq_add_neg]
      · rw [tendsto_pure_left]
        intro s hs
        rw [mob_coe, if_pos ht]
        exact mem_of_mem_nhds hs
    · have hev : ∀ᶠ x : ℝ in 𝓝 t, ent g 1 0 * x + ent g 1 1 ≠ 0 :=
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt.eventually_ne ht
      have hcont : ContinuousAt (fun x : ℝ => (((ent g 0 0 * x + ent g 0 1) /
          (ent g 1 0 * x + ent g 1 1) : ℝ) : OnePoint ℝ)) t := by
        apply continuous_coe.continuousAt.comp
        exact (((continuous_const.mul continuous_id).add continuous_const).continuousAt).div
          (((continuous_const.mul continuous_id).add continuous_const).continuousAt) ht
      refine hcont.congr (Filter.EventuallyEq.symm ?_)
      filter_upwards [hev] with x hx
      rw [mob_coe, if_neg hx]

/-! ### Identity theorem -/
/-- A scalar matrix acts trivially on the projective line. -/
lemma smul_eq_self_of_scalar (γ : GL (Fin 2) ℝ) (hγ : γ.val ∈ Set.range (Matrix.scalar (Fin 2)))
    (x : OnePoint ℝ) : γ • x = x := by
  obtain ⟨a, ha⟩ := hγ
  have h10 : γ 1 0 = 0 := by rw [← ha]; simp
  have h01 : γ 0 1 = 0 := by rw [← ha]; simp
  have h00 : γ 0 0 = a := by rw [← ha]; simp
  have h11 : γ 1 1 = a := by rw [← ha]; simp
  have hdet := γ.det_ne_zero
  rw [Matrix.det_fin_two] at hdet
  change γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 ≠ 0 at hdet
  have ha0 : a ≠ 0 := by
    intro h0
    apply hdet
    rw [h00, h11, h01, h10, h0]; ring
  cases x with
  | infty => rw [OnePoint.smul_infty_eq_self_iff]; exact h10
  | coe k =>
    rw [OnePoint.smul_some_eq_ite, h10, h11, h00, h01]
    simp [ha0]

/-- An element of `GL(2, ℝ)` fixing infinitely many real points acts trivially. -/
lemma smul_eq_self_of_infinite (γ : GL (Fin 2) ℝ)
    (hinf : {x : ℝ | γ • (x : OnePoint ℝ) = x}.Infinite) (z : OnePoint ℝ) : γ • z = z := by
  apply smul_eq_self_of_scalar
  rw [← Matrix.GeneralLinearGroup.fixpointPolynomial_eq_zero_iff]
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine hinf.mono fun x hx => ?_
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def] at hx ⊢
  have := (Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff (c := x) (g := γ)).2 hx
  simpa [Polynomial.aeval_def] using this

/-- Identity theorem: two Möbius maps agreeing near a real point are equal. -/
lemma mob_eq_of_eventually {g g' : Matrix.SpecialLinearGroup (Fin 2) A} {r : ℝ}
    (h' : ∀ᶠ x : ℝ in 𝓝 r, Monod.mob g (x : OnePoint ℝ) = Monod.mob g' x) (z : OnePoint ℝ) :
    Monod.mob g z = Monod.mob g' z := by
  have hinf : {x : ℝ | Monod.mob g (x : OnePoint ℝ) = Monod.mob g' x}.Infinite :=
    infinite_of_mem_nhds r h'
  have key := smul_eq_self_of_infinite ((Monod.slToGL A g')⁻¹ * Monod.slToGL A g)
    (hinf.mono fun x hx => by
      simp only [Set.mem_ofPred_eq, Monod.mob] at hx ⊢
      rw [mul_smul, hx, inv_smul_smul]) z
  rw [mul_smul, inv_smul_eq_iff] at key
  exact key

/-- A map that near every point of a preconnected set of reals agrees with some Möbius map
agrees with a single Möbius map on the whole set. -/
lemma exists_mob_eqOn (f : OnePoint ℝ → OnePoint ℝ) {I : Set ℝ} (hI : IsPreconnected I)
    {y0 : ℝ} (hy0 : y0 ∈ I)
    (hloc : ∀ y ∈ I, ∃ g : Matrix.SpecialLinearGroup (Fin 2) A,
      f =ᶠ[𝓝 (y : OnePoint ℝ)] Monod.mob g) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) A, ∀ y ∈ I, f y = Monod.mob g y := by
  classical
  let gs : ℝ → Matrix.SpecialLinearGroup (Fin 2) A :=
    fun y => if h : y ∈ I then (hloc y h).choose else 1
  have hgs : ∀ y ∈ I, f =ᶠ[𝓝 (y : OnePoint ℝ)] Monod.mob (gs y) := fun y hy => by
    simp only [gs, dif_pos hy]; exact (hloc y hy).choose_spec
  have hgs1 : ∀ y ∈ I, ∀ᶠ v : ℝ in 𝓝 y, f (v : OnePoint ℝ) = Monod.mob (gs y) v := fun y hy =>
    (continuous_coe.tendsto y).eventually (hgs y hy)
  let P : ℝ → ℝ → Prop := fun y z => ∀ x, Monod.mob (gs y) x = Monod.mob (gs z) x
  have hP : ∀ y z, y ∈ I → z ∈ I → P y z := by
    intro y z hy hz
    refine hI.induction₂' P ?_ ?_ hy hz
    · intro y hy
      rw [eventually_nhdsWithin_iff]
      filter_upwards [(hgs1 y hy).eventually_nhds] with z hz hzI
      have h3 : ∀ᶠ v : ℝ in 𝓝 z, Monod.mob (gs y) (v : OnePoint ℝ) = Monod.mob (gs z) v := by
        filter_upwards [hz, hgs1 z hzI] with v h1 h2
        rw [← h1, h2]
      have := mob_eq_of_eventually h3
      exact ⟨this, fun x => (this x).symm⟩
    · intro a b c _ _ _ hab hbc x
      rw [hab, hbc]
  refine ⟨gs y0, fun y hy => ?_⟩
  rw [(hgs y hy).self_of_nhds, hP y y0 hy hy0]

/-- Two continuous maps of `P¹` that agree on a set of reals belonging to a filter converging to
`x` agree at `x`. -/
lemma apply_eq_of_eqOn_filter {f k : OnePoint ℝ → OnePoint ℝ} (hf : Continuous f)
    (hk : Continuous k) {L : Filter ℝ} [L.NeBot] {x : OnePoint ℝ}
    (hL : map (fun y : ℝ => (y : OnePoint ℝ)) L ≤ 𝓝 x) {I : Set ℝ} (hI : I ∈ L)
    (heq : ∀ y ∈ I, f y = k y) : f x = k x := by
  have h1 : Tendsto (fun y : ℝ => f y) L (𝓝 (f x)) := hf.continuousAt.tendsto.comp hL
  have h2 : Tendsto (fun y : ℝ => k y) L (𝓝 (k x)) := hk.continuousAt.tendsto.comp hL
  exact tendsto_nhds_unique_of_eventuallyEq h1 h2 (eventually_of_mem hI heq)

lemma atTop_le_coe_nhds_infty :
    map (fun y : ℝ => (y : OnePoint ℝ)) atTop ≤ 𝓝 ∞ := by
  have h := tendsto_coe_infty (X := ℝ)
  rw [coclosedCompact_eq_cocompact] at h
  exact h.mono_left atTop_le_cocompact

/-- A map of `P¹` that is piecewise Möbius off a finite set `B` and continuous agrees at every
point with some Möbius map: at a point of `B`, use an adjacent interval free of `B`. -/
lemma exists_mob_apply_of_piecewise {f : OnePoint ℝ → OnePoint ℝ} (hf : Continuous f)
    (B : Finset (OnePoint ℝ))
    (hloc : ∀ x ∉ B, ∃ g : Matrix.SpecialLinearGroup (Fin 2) A, ∀ᶠ y in 𝓝 x, f y = Monod.mob g y)
    (x : OnePoint ℝ) : ∃ g : Matrix.SpecialLinearGroup (Fin 2) A, f x = Monod.mob g x := by
  by_cases hx : x ∈ B
  swap
  · obtain ⟨g, hg⟩ := hloc x hx
    exact ⟨g, hg.self_of_nhds⟩
  set S : Set ℝ := ((↑) : ℝ → OnePoint ℝ) ⁻¹' (B : Set (OnePoint ℝ)) with hS
  have hSfin : S.Finite := B.finite_toSet.preimage coe_injective.injOn
  -- a preconnected set of reals avoiding `S`, in a filter converging to `x`
  obtain ⟨L, hLne, I, hIL, hIc, hIS, hLx⟩ : ∃ L : Filter ℝ, L.NeBot ∧ ∃ I : Set ℝ, I ∈ L ∧
      IsPreconnected I ∧ (∀ y ∈ I, y ∉ S) ∧
      map (fun y : ℝ => (y : OnePoint ℝ)) L ≤ 𝓝 x := by
    cases x with
    | infty =>
      obtain ⟨M, hM⟩ := hSfin.bddAbove
      refine ⟨atTop, inferInstance, Ioi M, Ioi_mem_atTop M, isPreconnected_Ioi, ?_,
        atTop_le_coe_nhds_infty⟩
      intro y hy hyS
      exact absurd (hM hyS) (not_le.2 hy)
    | coe β =>
      have hT : (S \ {β})ᶜ ∈ 𝓝[>] β := by
        apply nhdsWithin_le_nhds
        apply (hSfin.sdiff.isClosed).isOpen_compl.mem_nhds
        simp
      obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (inter_mem hT self_mem_nhdsWithin)
      refine ⟨𝓝[>] β, inferInstance, Ioo β u, Ioo_mem_nhdsGT hu, isPreconnected_Ioo, ?_, ?_⟩
      · intro y hy hyS
        exact (hsub hy).1 ⟨hyS, ne_of_gt hy.1⟩
      · rw [nhds_coe_eq]
        exact map_mono nhdsWithin_le_nhds
  have hIne : I.Nonempty := Filter.nonempty_of_mem hIL
  obtain ⟨y0, hy0⟩ := hIne
  obtain ⟨g, hg⟩ := exists_mob_eqOn f hIc hy0 (fun y hy => hloc _ (hIS y hy))
  exact ⟨g, apply_eq_of_eqOn_filter hf (continuous_mob g) hLx hIL hg⟩

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
/-! ### The subring `ℚ` and `SL₂(ℚ)` are countable -/
instance countable_ratSubring' : Countable ratSubring := by
  have hs : Function.Surjective (fun q : ℚ => (⟨(q : ℝ), RingHom.mem_range_self _ q⟩ : ratSubring)) := by
    rintro ⟨x, hx⟩
    obtain ⟨q, rfl⟩ := RingHom.mem_range.1 hx
    exact ⟨q, rfl⟩
  exact hs.countable

instance countable_SLQ : Countable SLQ :=
  inferInstanceAs (Countable {M : Fin 2 → Fin 2 → ratSubring // Matrix.det M = 1})

lemma exists_rat_of_mem (x : ratSubring) : ∃ q : ℚ, (q : ℝ) = (x : ℝ) := by
  obtain ⟨q, hq⟩ := RingHom.mem_range.1 x.2
  exact ⟨q, hq⟩

/-! ### The irrational points -/
lemma volP1_apply (s : Set (OnePoint ℝ)) :
    Monod.volP1 s = volume (((↑) : ℝ → OnePoint ℝ) ⁻¹' s) :=
  (isOpenEmbedding_coe.measurableEmbedding).map_apply _ _

lemma compl_X0_subset : X0ᶜ ⊆ insert ∞ (range (fun q : ℚ => ((q : ℝ) : OnePoint ℝ))) := by
  intro x hx
  cases x with
  | infty => exact mem_insert _ _
  | coe r =>
    refine mem_insert_of_mem _ ?_
    have hr : ¬ Irrational r := fun hr => hx ⟨r, hr, rfl⟩
    unfold Irrational at hr
    obtain ⟨q, rfl⟩ := not_not.1 hr
    exact ⟨q, rfl⟩

lemma countable_compl_X0 : X0ᶜ.Countable :=
  ((countable_range _).insert ∞).mono compl_X0_subset

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part B: elements of `H_ℚ(ℚ)` at irrational points -/

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
theorem volP1_compl_X0 : Monod.volP1 X0ᶜ = 0 := by
  rw [volP1_apply]
  exact (countable_compl_X0.preimage coe_injective).measure_zero _

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
alias volP1_compl_X0 := ThompsonAmenability.M51.PartB.volP1_compl_X0

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
/-- A Möbius map with rational entries sends irrational points to irrational points. -/
lemma mob_mem_X0 (g : SLQ) {x : OnePoint ℝ} (hx : x ∈ X0) : Monod.mob g x ∈ X0 := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨a, ha⟩ := exists_rat_of_mem (g 0 0)
  obtain ⟨b, hb⟩ := exists_rat_of_mem (g 0 1)
  obtain ⟨c, hc⟩ := exists_rat_of_mem (g 1 0)
  obtain ⟨d, hd⟩ := exists_rat_of_mem (g 1 1)
  have hdet := det_ent g
  simp only [ent] at hdet
  rw [← ha, ← hb, ← hc, ← hd] at hdet
  have hdetq : a * d - b * c = 1 := by exact_mod_cast hdet
  have hden : (c : ℝ) * r + d ≠ 0 := by
    intro h0
    by_cases hc0 : c = 0
    · subst hc0
      have : (d : ℝ) = 0 := by simpa using h0
      have hd0 : d = 0 := by exact_mod_cast this
      rw [hd0] at hdetq; simp at hdetq
    · apply hr
      refine ⟨-d / c, ?_⟩
      have hc0' : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
      push_cast
      field_simp
      linarith
  rw [mob_coe, ent, ent, ent, ent, ← ha, ← hb, ← hc, ← hd, if_neg hden]
  refine ⟨_, ?_, rfl⟩
  rintro ⟨q, hq⟩
  have hlin : ((a : ℝ) - q * c) * r = q * d - b := by
    have hq' : (q : ℝ) * (c * r + d) = a * r + b := by rw [hq, div_mul_cancel₀ _ hden]
    linear_combination -hq'
  by_cases hq0 : a - q * c = 0
  · have h1 : (a : ℝ) - q * c = 0 := by exact_mod_cast hq0
    rw [h1, zero_mul] at hlin
    have h2 : q * d - b = 0 := by exact_mod_cast hlin.symm
    have : a * d - b * c = 0 := by linear_combination d * hq0 + c * h2
    rw [hdetq] at this; exact one_ne_zero this
  · apply hr
    refine ⟨(q * d - b) / (a - q * c), ?_⟩
    have hq0' : (a : ℝ) - q * c ≠ 0 := by exact_mod_cast hq0
    push_cast
    rw [div_eq_iff hq0', ← hlin]
    ring

theorem mob_mem_X0_iff (g : SLQ) (x : OnePoint ℝ) : Monod.mob g x ∈ X0 ↔ x ∈ X0 := by
  refine ⟨fun h => ?_, mob_mem_X0 g⟩
  have := mob_mem_X0 g⁻¹ h
  rwa [mob_inv_mob] at this

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
/-! ### Elements of `H_ℚ(ℚ)` at irrational points -/
/-- A generator of `H_ℚ(ℚ)` agrees at every point with a Möbius map of `SL₂(ℚ)`. -/
lemma gen_exists_mob {f : Hom} (hf : Monod.IsPiecewiseProjOn ratSubring Monod.ratPoints f)
    (x : OnePoint ℝ) : ∃ g : SLQ, f x = Monod.mob g x := by
  obtain ⟨B, -, hloc⟩ := hf
  exact exists_mob_apply_of_piecewise f.continuous B hloc x

/-- The property carried through the closure induction. -/
def Good (h : Hom) : Prop :=
  (∀ x, h x ∈ X0 ↔ x ∈ X0) ∧ ∀ x ∈ X0, ∃ g : SLQ, h x = Monod.mob g x

lemma good_of_mem_closure {h : Hom}
    (hh : h ∈ Subgroup.closure
      {f | f ∈ Monod.Gpp ∧ Monod.IsPiecewiseProjOn ratSubring Monod.ratPoints f}) :
    Good h := by
  induction hh using Subgroup.closure_induction with
  | mem f hf =>
    refine ⟨fun x => ?_, fun x _ => gen_exists_mob hf.2 x⟩
    obtain ⟨g, hg⟩ := gen_exists_mob hf.2 x
    rw [hg, mob_mem_X0_iff]
  | one => exact ⟨fun x => Iff.rfl, fun x _ => ⟨1, (mob_one x).symm⟩⟩
  | mul f k _ _ ihf ihk =>
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [Homeomorph.mul_apply, ihf.1, ihk.1]
    · obtain ⟨g, hg⟩ := ihk.2 x hx
      obtain ⟨g', hg'⟩ := ihf.2 (k x) ((ihk.1 x).2 hx)
      exact ⟨g' * g, by rw [Homeomorph.mul_apply, hg', hg, mob_mul]⟩
  | inv f _ ihf =>
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [Homeomorph.inv_apply, ← ihf.1, Homeomorph.apply_symm_apply]
    · have hy : f.symm x ∈ X0 := by rw [← ihf.1, Homeomorph.apply_symm_apply]; exact hx
      obtain ⟨g, hg⟩ := ihf.2 _ hy
      rw [Homeomorph.apply_symm_apply] at hg
      refine ⟨g⁻¹, ?_⟩
      have := mob_inv_mob g (f.symm x)
      rw [← hg] at this
      rw [Homeomorph.inv_apply, this]

theorem exists_mob_of_mem_HB {h : Hom} (hh : h ∈ HB ratSubring Monod.ratPoints)
    {x : OnePoint ℝ} (hx : x ∈ X0) : ∃ g : SLQ, h x = Monod.mob g x := by
  exact (good_of_mem_closure (Subgroup.mem_inf.1 hh).1).2 x hx

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
alias exists_mob_of_mem_HB := ThompsonAmenability.M51.PartB.exists_mob_of_mem_HB

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
/-! ### Null sets -/
/-- Möbius maps send null sets to null sets. -/
lemma null_image_mob {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A)
    {S : Set (OnePoint ℝ)} (hS : volume (((↑) : ℝ → OnePoint ℝ) ⁻¹' S) = 0) :
    volume (((↑) : ℝ → OnePoint ℝ) ⁻¹' (Monod.mob g '' S)) = 0 := by
  set a : ℝ := ((g 0 0 : A) : ℝ)
  set b : ℝ := ((g 0 1 : A) : ℝ)
  set c : ℝ := ((g 1 0 : A) : ℝ)
  set d : ℝ := ((g 1 1 : A) : ℝ)
  let φ : ℝ → ℝ := fun x => (a * x + b) / (c * x + d)
  let U : Set ℝ := {x | c * x + d ≠ 0}
  have hφ : DifferentiableOn ℝ φ (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact hx.2
  have h1 : volume (φ '' (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hφ
      (measure_mono_null Set.inter_subset_left hS)
  have hsub : ((↑) : ℝ → OnePoint ℝ) ⁻¹' (Monod.mob g '' S) ⊆
      φ '' (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U) ∪
        ((↑) : ℝ → OnePoint ℝ) ⁻¹' {Monod.mob g ∞} := by
    rintro y ⟨z, hz, hzy⟩
    cases z with
    | infty => exact Or.inr (by simp [← hzy])
    | coe x =>
      left
      rw [Monod.mob, OnePoint.smul_some_eq_ite] at hzy
      split_ifs at hzy with hx
      · exact absurd hzy.symm (OnePoint.coe_ne_infty y)
      · exact ⟨x, ⟨hz, hx⟩, OnePoint.coe_injective hzy⟩
  refine measure_mono_null hsub (measure_union_null h1 ?_)
  exact (Set.countable_singleton _).preimage OnePoint.coe_injective |>.measure_zero _

theorem null_preimage_mob (g : SLQ) {s : Set (OnePoint ℝ)} (hs : Monod.volP1 s = 0) :
    Monod.volP1 (Monod.mob g ⁻¹' s) = 0 := by
  rw [volP1_apply] at hs ⊢
  have e : Monod.mob g ⁻¹' s = Monod.mob g⁻¹ '' s := by
    ext x
    constructor
    · intro hx; exact ⟨Monod.mob g x, hx, mob_inv_mob g x⟩
    · rintro ⟨y, hy, rfl⟩
      show Monod.mob g (Monod.mob g⁻¹ y) ∈ s
      rwa [mob_mob_inv]
  rw [e]
  exact null_image_mob g⁻¹ hs

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
alias null_preimage_mob := ThompsonAmenability.M51.PartB.null_preimage_mob

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open Filter Topology Set OnePoint
namespace ThompsonAmenability.M51.PartC
variable {A : Subring ℝ}
/-!
# Part C: cut-and-paste

One explicit element `hS` of `H_ℚ(ℤ)` realises `y ↦ -1/y` on `(1, 2]`: it is the order
automorphism `psi` of `ℝ` (pieces `y - 2`, `-1/y`, `(y - 3)/(4 - y)`, `y - 3`, breakpoints `1, 2, 3`,
all in `SL₂(ℤ)`), extended to `P¹` fixing `∞`. With the rational affine maps
`aff a b : t ↦ a² t + a b` (Möbius maps of `!![a, b; 0, a⁻¹] ∈ SL₂(ℚ)`, in `H^{C¹}_ℚ(ℚ)`) it realises
`y ↦ -1/y` at every `y ≠ 0`, and then every `g ∈ SL₂(ℚ)` at every irrational point:
`g = τ_{a/c} ∘ S ∘ A_{c,d}` when `c ≠ 0`, `g = A_{a,b}` when `c = 0`.
-/
/-! ### Möbius maps: entries and formulas -/

/-! ### Order automorphisms of `ℝ`, extended to `P¹` -/

/-! ### The element `hS` -/

/-! ### The rational affine maps -/

/-! ### The countable subgroup `CC` -/

/-! ### Realising `y ↦ -1/y` -/

/-! ### Every `g ∈ SL₂(ℚ)` at every irrational point -/

end ThompsonAmenability.M51.PartC
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part C: cut-and-paste -/

end ThompsonAmenability.M51
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {X : Type*} (m : Set X → ℝ≥0∞)
/-!
# Part D: relative Zimmer (Monod 2023, Proposition 4.7), for means

If `Γ ≤ Λ` is co-amenable and the `Γ`-orbit relation is amenable, then any relation `R` agreeing
with the `Λ`-orbit relation on a conull saturated set (realised there by a countable set `C`) is
amenable.

Route.  After replacing `μ` by an equivalent finite measure:
* the invariant finitely additive probability on `Q = Λ ⧸ Γ` gives a mean `Mn` on bounded
  functions on `Q` (the upper Darboux integral, as in `MEAN_Bridge.lean`);
* for `λ ∈ Λ` and `g` bounded on `R` over `X₀`, `Fl λ g := P_Γ (g_λ) ∘ λ⁻¹`, where
  `g_λ (w, z) = g (λ w, z)` for `λ w ∈ X₀` (and `0` otherwise); up to null sets it depends only on
  the coset `λ Γ`;
* `P g ∈ L²(μ)` is the Riesz representative of `h ↦ Mn (q ↦ ⟪Fl (rep q) g, h⟫)`;
* the axioms follow from those of `P_Γ`; translation invariance `P (g ∘ κ⁻¹) = (P g) ∘ κ⁻¹`
  from the invariance of `Mn` under `Λ`; invariance under an arbitrary partial transformation
  `φ` from translation invariance and locality, on the countably many measurable pieces
  `{y | P g (φ⁻¹ y) = P g (κ⁻¹ y), g (φ⁻¹ y, c y) = g (κ⁻¹ y, c y) ∀ c ∈ C}`, `κ ∈ C`.
-/
/-! ## The mean on a set with a finitely additive probability (after `MEAN_Bridge.lean`) -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {X : Type*} (m : Set X → ℝ≥0∞)
variable {m}

/-! ### The upper integral on `ℓ∞` -/
local notation "E" X => lp (fun _ : X => ℝ) ∞

/-- A finitely valued function as an element of `ℓ∞`. -/
noncomputable def meanOfFin (s : X → ℝ) (hs : (range s).Finite) : E X :=
  ⟨s, memℓp_infty_iff.2 (by
    have : (range fun i => ‖s i‖) = (fun v => ‖v‖) '' range s := by
      rw [← Set.range_comp]; rfl
    rw [this]
    exact (hs.image _).bddAbove)⟩

@[simp] theorem meanOfFin_apply (s : X → ℝ) (hs : (range s).Finite) (x : X) :
    (meanOfFin s hs : X → ℝ) x = s x := rfl

theorem mean_range_indicator (A : Set X) : (range (A.indicator (1 : X → ℝ))).Finite :=
  (Set.toFinite ({0, 1} : Set ℝ)).subset (by
    rintro _ ⟨x, rfl⟩; by_cases h : x ∈ A <;> simp [h])

/-- The indicator function of `A` as an element of `ℓ∞`. -/
noncomputable def mean_ind (A : Set X) : E X := meanOfFin _ (mean_range_indicator A)

@[simp] theorem mean_ind_apply (A : Set X) (x : X) :
    (mean_ind A : X → ℝ) x = A.indicator 1 x := rfl

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {Q : Type*}
/-! ### The mean as a function on bounded functions -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {Q : Type*}
variable {m} (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
include hm h1

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
open Monod
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
/-! ## Generic facts about left invariant means -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
open Monod
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {R : Set (X × X)} {P : (X × X → ℝ) → X → ℝ}

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
open Monod
variable {X : Type*} [MeasurableSpace X] {R : Set (X × X)} (φ : PartialTransformation R)
/-! ## Partial transformations -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
/-! ## Integration helpers -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-! ## Riesz representation -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
/-! ## The data of the relative Zimmer theorem -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
namespace Data
open Monod Classical
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : Type*} [Group G] [MulAction G X]

end Data
end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
namespace Data
open Monod Classical
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : Type*} [Group G] [MulAction G X]
variable {g g' : X × X → ℝ} {C C' : ℝ}
/-! ### The functions `F_λ` -/

end Data
end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
namespace Data
open Monod Classical
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : Type*} [Group G] [MulAction G X]
variable [IsFiniteMeasure μ] {g g' : X × X → ℝ} {C C' : ℝ}
/-! ### The mean `P` -/

/-! ### The axioms of a mean -/

/-! ### Invariance under the partial transformations of `R` -/

end Data
end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
/-! ## The theorem -/

end ThompsonAmenability.M51.PartD
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part D: relative Zimmer (Monod 2023, Proposition 4.7) -/

/-! ## Part E1: Thompson's group `F` at non-dyadic points -/
/-- A non-dyadic point of `(0,1)`. -/
def NonDyadic (t : ℝ) : Prop := 0 < t ∧ t < 1 ∧ ¬ CannonFloydParry.IsDyadic t

/-- `s` is the image of `t` under a dyadic affine map `y ↦ 2ⁿ y + b`, `b` dyadic. -/
def DAff (s t : ℝ) : Prop := ∃ (n : ℤ) (b : ℝ), CannonFloydParry.IsDyadic b ∧ s = 2 ^ n * t + b

end ThompsonAmenability.M51
end

section
namespace ThompsonAmenability.M51.PartE1
open CannonFloydParry
/-!
# Part E1: Thompson's group `F` at non-dyadic points

* `F_apply_nonDyadic_daff`: at a non-dyadic point `t ∈ (0,1)` an element of `F` acts by a dyadic
  affine map `y ↦ 2ⁿ y + c` (`c` dyadic), and the image is again non-dyadic in `(0,1)`.
* `exists_F_of_daff`: two non-dyadic points of `(0,1)` related by a dyadic affine map lie in one
  `F`-orbit: glue the affine map on a small dyadic interval around `t` to an element of `F` that
  agrees with it at the two endpoints (`exists_mem_F_map_partition`).
-/
/-! ### Dyadic rationals -/
lemma isDyadic_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma isDyadic_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma isDyadic_sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  simpa [sub_eq_add_neg] using isDyadic_add hx (isDyadic_neg hy)

lemma isDyadic_zpow_mul {n : ℤ} {x : ℝ} (hx : IsDyadic x) : IsDyadic (2 ^ n * x) := by
  obtain ⟨m, k, rfl⟩ := hx
  by_cases hn : 0 ≤ n
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine ⟨m * 2 ^ j, k, ?_⟩
    push_cast
    rw [zpow_natCast]
    ring
  · push Not at hn
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j : ℤ) := ⟨(-n).toNat, by omega⟩
    refine ⟨m, k + j, ?_⟩
    rw [zpow_neg, zpow_natCast]
    field_simp
    ring

lemma isDyadic_zero : IsDyadic 0 := ⟨0, 0, by simp⟩

lemma isDyadic_one : IsDyadic 1 := ⟨1, 0, by simp⟩

/-- Between any two reals there is a dyadic rational. -/
lemma exists_isDyadic_Ioo {a b : ℝ} (hab : a < b) : ∃ c : ℝ, IsDyadic c ∧ a < c ∧ c < b := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 : ℝ) / 2 ^ k < b - a := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hab) (by norm_num : (1:ℝ)/2 < 1)
    exact ⟨k, by simpa [div_pow, one_div] using hk⟩
  have hP : (0 : ℝ) < 2 ^ k := by positivity
  have hwide : (1 : ℝ) < (b - a) * 2 ^ k := by
    rw [div_lt_iff₀ hP] at hk
    linarith
  have hfl : ((⌊a * 2 ^ k⌋ : ℤ) : ℝ) ≤ a * 2 ^ k := Int.floor_le _
  have hfu : a * 2 ^ k < ((⌊a * 2 ^ k⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  refine ⟨((⌊a * 2 ^ k⌋ + 1 : ℤ) : ℝ) / 2 ^ k, ⟨⌊a * 2 ^ k⌋ + 1, k, rfl⟩, ?_, ?_⟩
  · rw [lt_div_iff₀ hP]
    push_cast
    linarith
  · rw [div_lt_iff₀ hP]
    push_cast
    linarith

/-- If `t` is not dyadic, neither is `2ⁿ t + c` for dyadic `c`. -/
lemma not_isDyadic_affine {n : ℤ} {c t : ℝ} (hc : IsDyadic c) (ht : ¬ IsDyadic t) :
    ¬ IsDyadic (2 ^ n * t + c) := by
  intro h
  apply ht
  have h2 : IsDyadic (2 ^ (-n) * ((2 ^ n * t + c) - c)) := isDyadic_zpow_mul (isDyadic_sub h hc)
  have he : (2 : ℝ) ^ (-n) * ((2 ^ n * t + c) - c) = t := by
    rw [add_sub_cancel_right, ← mul_assoc, ← zpow_add₀ (two_ne_zero), neg_add_cancel, zpow_zero,
      one_mul]
  rwa [he] at h2

/-! ### Gaps in a finite set -/
/-- Around any point outside a finite set there is a two-sided interval missing the set. -/
lemma exists_gap_around {B : Finset ℝ} {x : ℝ} (hx : x ∉ (B : Set ℝ)) :
    ∃ ε > 0, Set.Ioo (x - ε) (x + ε) ∩ (B : Set ℝ) = ∅ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp B.finite_toSet.isClosed.isOpen_compl x hx
  refine ⟨ε, hε, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false, iff_false,
    not_and]
  rintro ⟨hz1, hz2⟩ hzB
  exact hball (by rw [Real.ball_eq_Ioo]; exact ⟨hz1, hz2⟩) hzB

/-! ### `extend` -/
lemma extend_coe (f : UI ≃o UI) (z : UI) : extend f (z : ℝ) = (f z : ℝ) := by
  rw [extend_apply, extendFun_of_mem f z.2]

lemma extend_of_mem (f : UI ≃o UI) {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    extend f z = (f ⟨z, hz⟩ : ℝ) := by
  rw [extend_apply, extendFun_of_mem f hz]

lemma apply_zero (f : UI ≃o UI) : (f ⟨0, zero_mem_UI⟩ : ℝ) = 0 := by
  have h : f ⟨0, zero_mem_UI⟩ ≤ f (f.symm ⟨0, zero_mem_UI⟩) :=
    f.monotone (show (⟨0, zero_mem_UI⟩ : UI) ≤ f.symm ⟨0, zero_mem_UI⟩ from
      (f.symm ⟨0, zero_mem_UI⟩).2.1)
  rw [f.apply_symm_apply] at h
  exact le_antisymm h (f ⟨0, zero_mem_UI⟩).2.1

lemma apply_one (f : UI ≃o UI) : (f ⟨1, one_mem_UI⟩ : ℝ) = 1 := by
  have h : f (f.symm ⟨1, one_mem_UI⟩) ≤ f ⟨1, one_mem_UI⟩ :=
    f.monotone (show f.symm ⟨1, one_mem_UI⟩ ≤ (⟨1, one_mem_UI⟩ : UI) from
      (f.symm ⟨1, one_mem_UI⟩).2.2)
  rw [f.apply_symm_apply] at h
  exact le_antisymm (f ⟨1, one_mem_UI⟩).2.2 h

lemma extend_of_nonpos (f : UI ≃o UI) {z : ℝ} (hz : z ≤ 0) : extend f z = z := by
  rcases hz.lt_or_eq with hz | rfl
  · rw [extend_apply, extendFun_of_notMem f (fun h => absurd h.1 (not_le.mpr hz))]
  · rw [extend_of_mem f zero_mem_UI, apply_zero]

lemma extend_of_one_le (f : UI ≃o UI) {z : ℝ} (hz : 1 ≤ z) : extend f z = z := by
  rcases hz.lt_or_eq with hz | rfl
  · rw [extend_apply, extendFun_of_notMem f (fun h => absurd h.2 (not_le.mpr hz))]
  · rw [extend_of_mem f one_mem_UI, apply_one]

/-! ### Target 1 -/
/-- At a non-dyadic point an element of `F` acts by a dyadic affine map. -/
theorem F_apply_nonDyadic_daff {g : CannonFloydParry.UI ≃o CannonFloydParry.UI}
    (hg : g ∈ CannonFloydParry.F) {t : ℝ} (ht : NonDyadic t) :
    NonDyadic (CannonFloydParry.extend g t) ∧ DAff (CannonFloydParry.extend g t) t := by
  obtain ⟨B, hBd, hB⟩ := mem_F_iff_isThompson.mp hg
  obtain ⟨ht0, ht1, htd⟩ := ht
  have htB : t ∉ (B : Set ℝ) := fun h => htd (hBd t h)
  obtain ⟨ε, hε, hgap⟩ := exists_gap_around htB
  obtain ⟨x, hxd, hx1, hx2⟩ := exists_isDyadic_Ioo (show max (t - ε) 0 < t from
    max_lt (by linarith) ht0)
  obtain ⟨y, -, hy1, hy2⟩ := exists_isDyadic_Ioo (show t < min (t + ε) 1 from
    lt_min (by linarith) ht1)
  have hxε : t - ε < x := lt_of_le_of_lt (le_max_left _ _) hx1
  have hx0 : 0 < x := lt_of_le_of_lt (le_max_right _ _) hx1
  have hyε : y < t + ε := lt_of_lt_of_le hy2 (min_le_left _ _)
  have hy1' : y < 1 := lt_of_lt_of_le hy2 (min_le_right _ _)
  have hxI : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx0.le, by linarith⟩
  have hyI : y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, hy1'.le⟩
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hgap' : Set.Ioo ((⟨x, hxI⟩ : UI) : ℝ) ((⟨y, hyI⟩ : UI) : ℝ) ∩ (B : Set ℝ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem] at hgap ⊢
    intro z hz
    exact hgap z ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  obtain ⟨n, c, hnc⟩ := hB ⟨x, hxI⟩ ⟨y, hyI⟩ (show x < y by linarith) hgap'
  have hgx := hnc ⟨x, hxI⟩ ⟨le_rfl, by show x ≤ y; linarith⟩
  have hgt := hnc ⟨t, htI⟩ ⟨by show x ≤ t; linarith, by show t ≤ y; linarith⟩
  have hgxd : IsDyadic (g ⟨x, hxI⟩ : ℝ) := (bijOn_dyadic hg).mapsTo hxd
  have hcd : IsDyadic c := by
    have hc : c = (g ⟨x, hxI⟩ : ℝ) - 2 ^ n * x := by rw [hgx]; ring
    rw [hc]
    exact isDyadic_sub hgxd (isDyadic_zpow_mul hxd)
  have hext : extend g t = 2 ^ n * t + c := by rw [extend_of_mem g htI]; exact hgt
  have hnd : ¬ IsDyadic (extend g t) := by rw [hext]; exact not_isDyadic_affine hcd htd
  have hmem : extend g t ∈ Set.Icc (0:ℝ) 1 := by
    rw [extend_of_mem g htI]; exact (g ⟨t, htI⟩).2
  refine ⟨⟨?_, ?_, hnd⟩, ⟨n, c, hcd, hext⟩⟩
  · rcases hmem.1.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ isDyadic_zero) hnd
  · rcases hmem.2.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ isDyadic_one) hnd

end ThompsonAmenability.M51.PartE1
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
alias F_apply_nonDyadic_daff := ThompsonAmenability.M51.PartE1.F_apply_nonDyadic_daff

end ThompsonAmenability.M51
end

section
namespace ThompsonAmenability.M51.PartE1
open CannonFloydParry
/-! ### Gluing an affine piece into an element of `F` -/
/-- An element `f ∈ F` that agrees with the dyadic affine map `A z = 2ⁿ z + b` at the dyadic
points `p < q` of `(0,1)` can be modified to an element of `F` equal to `A` on `[p, q]`. -/
lemma exists_mem_F_eq_affine_on {f : UI ≃o UI} (hf : f ∈ F) {p q : ℝ} (hp0 : 0 < p)
    (hpq : p < q) (hq1 : q < 1) (hpd : IsDyadic p) (hqd : IsDyadic q) (n : ℤ) (b : ℝ)
    (hfp : extend f p = 2 ^ n * p + b) (hfq : extend f q = 2 ^ n * q + b) :
    ∃ g ∈ F, ∀ z ∈ Set.Icc p q, extend g z = 2 ^ n * z + b := by
  classical
  have ha : (0:ℝ) < 2 ^ n := zpow_pos two_pos n
  let L0 : ℝ → ℝ := fun z => if z ∈ Set.Icc p q then 2 ^ n * z + b else extend f z
  have hin : ∀ z ∈ Set.Icc p q, L0 z = 2 ^ n * z + b := fun z hz => if_pos hz
  have hout : ∀ z, z ∉ Set.Ioo p q → L0 z = extend f z := by
    intro z hz
    by_cases hzI : z ∈ Set.Icc p q
    · rw [hin z hzI]
      rcases hzI.1.lt_or_eq with h1 | h1
      · rcases hzI.2.lt_or_eq with h2 | h2
        · exact absurd ⟨h1, h2⟩ hz
        · rw [h2, hfq]
      · rw [← h1, hfp]
    · exact if_neg hzI
  have hfmono : StrictMono (extend f) := (extend f).strictMono
  have hmono : StrictMono L0 := by
    intro z w hzw
    by_cases hz : z ∈ Set.Icc p q <;> by_cases hw : w ∈ Set.Icc p q
    · rw [hin z hz, hin w hw]
      have := mul_lt_mul_of_pos_left hzw ha
      linarith
    · have hwq : q < w := by
        by_contra hcon
        exact hw ⟨by linarith [hz.1], not_lt.mp hcon⟩
      rw [hin z hz, hout w (fun h => by linarith [h.2])]
      have h1 : 2 ^ n * z ≤ 2 ^ n * q := mul_le_mul_of_nonneg_left hz.2 ha.le
      have h2 := hfmono hwq
      rw [hfq] at h2
      linarith
    · have hzp : z < p := by
        by_contra hcon
        exact hz ⟨not_lt.mp hcon, by linarith [hw.2]⟩
      rw [hin w hw, hout z (fun h => by linarith [h.1])]
      have h1 : 2 ^ n * p ≤ 2 ^ n * w := mul_le_mul_of_nonneg_left hw.1 ha.le
      have h2 := hfmono hzp
      rw [hfp] at h2
      linarith
    · rw [hout z (fun h => hz (Set.Ioo_subset_Icc_self h)),
        hout w (fun h => hw (Set.Ioo_subset_Icc_self h))]
      exact hfmono hzw
  have hsurj : Function.Surjective L0 := by
    intro y
    by_cases hy : y ∈ Set.Icc (2 ^ n * p + b) (2 ^ n * q + b)
    · refine ⟨(y - b) / 2 ^ n, ?_⟩
      have hzI : (y - b) / 2 ^ n ∈ Set.Icc p q := by
        constructor
        · rw [le_div_iff₀ ha]; linarith [hy.1]
        · rw [div_le_iff₀ ha]; linarith [hy.2]
      rw [hin _ hzI]
      field_simp
      ring
    · refine ⟨(extend f).symm y, ?_⟩
      have hz : (extend f).symm y ∉ Set.Ioo p q := by
        intro h
        apply hy
        have h1 := hfmono h.1
        have h2 := hfmono h.2
        rw [OrderIso.apply_symm_apply, hfp] at h1
        rw [OrderIso.apply_symm_apply, hfq] at h2
        exact ⟨h1.le, h2.le⟩
      rw [hout _ hz, OrderIso.apply_symm_apply]
  let L : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective L0 hmono hsurj
  have hL : ∀ z, L z = L0 z := fun z => rfl
  have hlo : ∀ z ≤ (0:ℝ), L z = z := by
    intro z hz
    rw [hL, hout z (fun h => by linarith [h.1]), extend_of_nonpos f hz]
  have hhi : ∀ z, (1:ℝ) ≤ z → L z = z := by
    intro z hz
    rw [hL, hout z (fun h => by linarith [h.2]), extend_of_one_le f hz]
  refine ⟨restrict L hlo hhi, ?_, ?_⟩
  · apply mem_F_iff_isThompson.mpr
    obtain ⟨Bf, hBfd, hBf⟩ := mem_F_iff_isThompson.mp hf
    refine ⟨insert p (insert q Bf), ?_, ?_⟩
    · intro c hc
      simp only [Finset.mem_insert] at hc
      rcases hc with rfl | rfl | hc
      · exact hpd
      · exact hqd
      · exact hBfd c hc
    · intro x y hxy hgap
      have hpn : p ∉ Set.Ioo (x : ℝ) (y : ℝ) := fun h =>
        (Set.eq_empty_iff_forall_notMem.mp hgap) p ⟨h, by simp⟩
      have hqn : q ∉ Set.Ioo (x : ℝ) (y : ℝ) := fun h =>
        (Set.eq_empty_iff_forall_notMem.mp hgap) q ⟨h, by simp⟩
      have hgapf : Set.Ioo (x : ℝ) (y : ℝ) ∩ (Bf : Set ℝ) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem] at hgap ⊢
        intro z hz
        exact hgap z ⟨hz.1, by simp [hz.2]⟩
      by_cases hcase : (y : ℝ) ≤ p ∨ q ≤ (x : ℝ)
      · obtain ⟨m, c, hmc⟩ := hBf x y hxy hgapf
        refine ⟨m, c, fun z hz => ?_⟩
        have hzo : (z : ℝ) ∉ Set.Ioo p q := by
          intro h
          rcases hcase with h' | h'
          · linarith [hz.2, h.1]
          · linarith [hz.1, h.2]
        rw [restrict_coe, hL, hout _ hzo, extend_coe]
        exact hmc z hz
      · push Not at hcase
        obtain ⟨hpy, hxq⟩ := hcase
        have hpx : p ≤ (x : ℝ) := by
          by_contra hcon
          exact hpn ⟨lt_of_not_ge hcon, hpy⟩
        have hyq : (y : ℝ) ≤ q := by
          by_contra hcon
          exact hqn ⟨hxq, lt_of_not_ge hcon⟩
        refine ⟨n, b, fun z hz => ?_⟩
        rw [restrict_coe, hL]
        exact hin _ ⟨le_trans hpx hz.1, le_trans hz.2 hyq⟩
  · intro z hz
    have hzI : z ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rw [extend_of_mem _ hzI, restrict_coe, hL]
    exact hin z hz

/-! ### Target 2 -/
/-- Two non-dyadic points related by a dyadic affine map lie in one `F`-orbit. -/
theorem exists_F_of_daff {s t : ℝ} (hs : NonDyadic s) (ht : NonDyadic t) (h : DAff s t) :
    ∃ g ∈ CannonFloydParry.F, CannonFloydParry.extend g t = s := by
  obtain ⟨n, b, hb, rfl⟩ := h
  obtain ⟨hs0, hs1, -⟩ := hs
  obtain ⟨ht0, ht1, -⟩ := ht
  have ha : (0:ℝ) < 2 ^ n := zpow_pos two_pos n
  set a : ℝ := 2 ^ n with ha_def
  set ε : ℝ := min (min t (1 - t)) (min (a * t + b) (1 - (a * t + b)) / a) with hε_def
  have hε : 0 < ε := lt_min (lt_min ht0 (by linarith)) (div_pos (lt_min hs0 (by linarith)) ha)
  have hεt : ε ≤ t := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε1 : ε ≤ 1 - t := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεa : a * ε ≤ min (a * t + b) (1 - (a * t + b)) := by
    have : ε ≤ min (a * t + b) (1 - (a * t + b)) / a := min_le_right _ _
    rw [le_div_iff₀ ha] at this
    linarith
  have hεs : a * ε ≤ a * t + b := le_trans hεa (min_le_left _ _)
  have hεs1 : a * ε ≤ 1 - (a * t + b) := le_trans hεa (min_le_right _ _)
  obtain ⟨p, hpd, hp1, hp2⟩ := exists_isDyadic_Ioo (show t - ε < t by linarith)
  obtain ⟨q, hqd, hq1, hq2⟩ := exists_isDyadic_Ioo (show t < t + ε by linarith)
  have hp0 : 0 < p := by linarith
  have hq1' : q < 1 := by linarith
  have hAp : a * (t - ε) < a * p := mul_lt_mul_of_pos_left hp1 ha
  have hAq : a * q < a * (t + ε) := mul_lt_mul_of_pos_left hq2 ha
  have hApq : a * p < a * q := mul_lt_mul_of_pos_left (by linarith) ha
  have hAp0 : 0 < a * p + b := by nlinarith
  have hAq1 : a * q + b < 1 := by nlinarith
  have hApd : IsDyadic (a * p + b) := isDyadic_add (isDyadic_zpow_mul hpd) hb
  have hAqd : IsDyadic (a * q + b) := isDyadic_add (isDyadic_zpow_mul hqd) hb
  -- the two partitions `0 < p < q < 1` and `0 < A p < A q < 1`
  let x : Fin 4 → UI := ![⟨0, zero_mem_UI⟩, ⟨p, hp0.le, by linarith⟩, ⟨q, by linarith, hq1'.le⟩,
    ⟨1, one_mem_UI⟩]
  let y : Fin 4 → UI := ![⟨0, zero_mem_UI⟩, ⟨a * p + b, hAp0.le, by linarith⟩,
    ⟨a * q + b, by linarith, hAq1.le⟩, ⟨1, one_mem_UI⟩]
  have hx : StrictMono x := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · show (0:ℝ) < p; exact hp0
    · show p < q; linarith
    · show q < 1; exact hq1'
  have hy : StrictMono y := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · show (0:ℝ) < a * p + b; exact hAp0
    · show a * p + b < a * q + b; linarith
    · show a * q + b < 1; exact hAq1
  have hxd : ∀ i, IsDyadic (x i : ℝ) := by
    intro i
    fin_cases i
    · exact isDyadic_zero
    · exact hpd
    · exact hqd
    · exact isDyadic_one
  have hyd : ∀ i, IsDyadic (y i : ℝ) := by
    intro i
    fin_cases i
    · exact isDyadic_zero
    · exact hApd
    · exact hAqd
    · exact isDyadic_one
  obtain ⟨f, hfF, hfxy⟩ := exists_mem_F_map_partition (n := 3) x y hx hy rfl rfl rfl rfl hxd hyd
  have hfp : extend f p = a * p + b := by
    have := congrArg Subtype.val (hfxy 1)
    rw [extend_of_mem f ⟨hp0.le, by linarith⟩]
    exact this
  have hfq : extend f q = a * q + b := by
    have := congrArg Subtype.val (hfxy 2)
    rw [extend_of_mem f ⟨by linarith, hq1'.le⟩]
    exact this
  obtain ⟨g, hgF, hg⟩ := exists_mem_F_eq_affine_on hfF hp0 (by linarith) hq1' hpd hqd n b hfp hfq
  exact ⟨g, hgF, hg t ⟨hp2.le, hq1.le⟩⟩

end ThompsonAmenability.M51.PartE1
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
alias exists_F_of_daff := ThompsonAmenability.M51.PartE1.exists_F_of_daff

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
/-!
# Part E2: the orbit relation of `H_ℚ(ℤ)` on `P¹` is amenable

Route. The published conjugacy `Monod.contDiff_and_exists_mulEquiv_HRat_F` gives `c` (strictly
monotone from `(0,1)` onto `ℝ`) and `φ : HRat ≃* F` with `h (c t) = c (extend (φ h) t)`.
* `alpha : ℝ → (0,1)` is an increasing bijection that is dyadic affine on every `[n, n+1]`
  (`alpha y = 2^e y + b`, `b` dyadic), so `Psi := c ∘ alpha` is an order isomorphism of `ℝ`.
* `Aff` is the group of dyadic affine maps `y ↦ 2ⁿ y + b` of `ℝ`: countable and solvable, hence
  amenable; it acts on `P¹` through `Psi` (the subgroup `Lam` of homeomorphisms of `P¹`).
* On the conull set `X1 = c '' (non-dyadic points)`, the `Lam`-orbits and the `HRat`-orbits
  coincide (Blueprint `F_apply_nonDyadic_daff`, `exists_F_of_daff`), so `Lam` preserves null sets
  (Blueprint `exists_mob_of_mem_HB`, `null_preimage_mob`), the published C1 theorem makes the
  `Lam`-orbit relation amenable, and the Blueprint's `isAmenableRel_of_agree` transfers it.
-/
/-! ## Section 1: dyadic rationals -/
lemma isDyadic_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma isDyadic_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma isDyadic_sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  rw [sub_eq_add_neg]; exact isDyadic_add hx (isDyadic_neg hy)

lemma isDyadic_zpow_mul {n : ℤ} {x : ℝ} (hx : IsDyadic x) : IsDyadic (2 ^ n * x) := by
  obtain ⟨m, k, rfl⟩ := hx
  by_cases hn : 0 ≤ n
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine ⟨m * 2 ^ j, k, ?_⟩
    push_cast
    rw [zpow_natCast]
    ring
  · push Not at hn
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j : ℤ) := ⟨(-n).toNat, by omega⟩
    refine ⟨m, k + j, ?_⟩
    rw [zpow_neg, zpow_natCast]
    field_simp
    ring

lemma isDyadic_intCast (m : ℤ) : IsDyadic (m : ℝ) := ⟨m, 0, by simp⟩

lemma isDyadic_zero : IsDyadic 0 := by simpa using isDyadic_intCast 0

lemma isDyadic_zpow (n : ℤ) : IsDyadic ((2 : ℝ) ^ n) := by
  simpa using isDyadic_zpow_mul (n := n) (isDyadic_intCast 1)

lemma countable_isDyadic : {x : ℝ | IsDyadic x}.Countable := by
  have : {x : ℝ | IsDyadic x} = Set.range (fun p : ℤ × ℕ => (p.1 : ℝ) / 2 ^ p.2) := by
    ext x
    simp only [Set.mem_range, Prod.exists, IsDyadic]
    constructor
    · rintro ⟨m, k, rfl⟩; exact ⟨m, k, rfl⟩
    · rintro ⟨m, k, rfl⟩; exact ⟨m, k, rfl⟩
  rw [this]
  exact Set.countable_range _

/-! ## Section 2: the dyadic affine relation `DAff` -/

lemma daff_symm {s t : ℝ} (h : DAff s t) : DAff t s := by
  obtain ⟨n, b, hb, rfl⟩ := h
  refine ⟨-n, -(2 ^ (-n) * b), isDyadic_neg (isDyadic_zpow_mul hb), ?_⟩
  rw [mul_add, ← mul_assoc, ← zpow_add₀ two_ne_zero]
  simp

lemma daff_trans {r s t : ℝ} (h1 : DAff r s) (h2 : DAff s t) : DAff r t := by
  obtain ⟨n, b, hb, rfl⟩ := h1
  obtain ⟨m, b', hb', rfl⟩ := h2
  refine ⟨n + m, 2 ^ n * b' + b, isDyadic_add (isDyadic_zpow_mul hb') hb, ?_⟩
  rw [zpow_add₀ two_ne_zero]
  ring

lemma isDyadic_of_daff {s t : ℝ} (h : DAff s t) (ht : IsDyadic t) : IsDyadic s := by
  obtain ⟨n, b, hb, rfl⟩ := h
  exact isDyadic_add (isDyadic_zpow_mul ht) hb

/-! ## Section 3: the increasing dyadic bijection `alpha : ℝ → (0,1)` -/
/-- The knots: `2^(n-1)` for `n ≤ 0`, `1 - 2^(-n-1)` for `n ≥ 0`. -/
noncomputable def knot (n : ℤ) : ℝ := if n ≤ 0 then 2 ^ (n - 1) else 1 - 2 ^ (-n - 1)

/-- The exponent of the slope on `[n, n+1]`. -/
def ex (n : ℤ) : ℤ := if n < 0 then n - 1 else -n - 2

lemma knot_succ (n : ℤ) : knot (n + 1) = knot n + 2 ^ ex n := by
  unfold knot ex
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [if_pos (by omega), if_pos hn.le, if_pos hn]
    have : n + 1 - 1 = (n - 1) + 1 := by ring
    rw [this, zpow_add_one₀ two_ne_zero]
    ring
  · norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have h1 : -(n + 1) - 1 = -n - 2 := by ring
    have h2 : -n - 1 = (-n - 2) + 1 := by ring
    rw [h1, h2, zpow_add_one₀ two_ne_zero]
    ring

lemma knot_pos (n : ℤ) : 0 < knot n := by
  unfold knot
  split_ifs with h
  · positivity
  · have : (2 : ℝ) ^ (-n - 1) < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by omega)
    linarith

lemma knot_lt_one (n : ℤ) : knot n < 1 := by
  unfold knot
  split_ifs with h
  · exact zpow_lt_one_of_neg₀ (by norm_num) (by omega)
  · have : (0 : ℝ) < 2 ^ (-n - 1) := by positivity
    linarith

lemma knot_strictMono : StrictMono knot :=
  strictMono_int_of_lt_succ fun n => by rw [knot_succ]; linarith [zpow_pos (two_pos (α := ℝ)) (ex n)]

lemma isDyadic_knot (n : ℤ) : IsDyadic (knot n) := by
  unfold knot
  split_ifs
  · exact isDyadic_zpow _
  · exact isDyadic_sub (by simpa using isDyadic_intCast 1) (isDyadic_zpow _)

/-- The increasing bijection `ℝ → (0,1)`, affine with slope `2 ^ ex n` on `[n, n+1]`. -/
noncomputable def alpha (y : ℝ) : ℝ := knot ⌊y⌋ + (y - ⌊y⌋) * 2 ^ ex ⌊y⌋

lemma knot_le_alpha (y : ℝ) : knot ⌊y⌋ ≤ alpha y := by
  unfold alpha
  have := Int.floor_le y
  have : (0 : ℝ) < 2 ^ ex ⌊y⌋ := by positivity
  nlinarith

lemma alpha_lt_knot (y : ℝ) : alpha y < knot (⌊y⌋ + 1) := by
  unfold alpha
  rw [knot_succ]
  have := Int.lt_floor_add_one y
  have : (0 : ℝ) < 2 ^ ex ⌊y⌋ := by positivity
  nlinarith

lemma alpha_strictMono : StrictMono alpha := by
  intro y z hyz
  rcases (Int.floor_mono hyz.le).eq_or_lt with h | h
  · unfold alpha
    rw [h]
    have : (0 : ℝ) < 2 ^ ex ⌊z⌋ := by positivity
    nlinarith
  · calc alpha y < knot (⌊y⌋ + 1) := alpha_lt_knot y
      _ ≤ knot ⌊z⌋ := knot_strictMono.monotone (by omega)
      _ ≤ alpha z := knot_le_alpha z

lemma alpha_mem (y : ℝ) : alpha y ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨(knot_pos _).trans_le (knot_le_alpha y), (alpha_lt_knot y).trans (knot_lt_one _)⟩

lemma daff_alpha (y : ℝ) : DAff (alpha y) y := by
  refine ⟨ex ⌊y⌋, knot ⌊y⌋ - 2 ^ ex ⌊y⌋ * (⌊y⌋ : ℝ),
    isDyadic_sub (isDyadic_knot _) (isDyadic_zpow_mul (isDyadic_intCast _)), ?_⟩
  unfold alpha
  ring

lemma alpha_surj {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : ∃ y, alpha y = t := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr ht1) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨k', hk'⟩ := exists_pow_lt_of_lt_one ht0 (by norm_num : (1 / 2 : ℝ) < 1)
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, knot z ≤ t → z ≤ b := by
    refine ⟨k, fun z hz => ?_⟩
    by_contra hzk
    push Not at hzk
    have hz0 : ¬ z ≤ 0 := by omega
    unfold knot at hz
    rw [if_neg hz0] at hz
    have : (2 : ℝ) ^ (-z - 1) ≤ (1 / 2) ^ k := by
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  have hne : ∃ z : ℤ, knot z ≤ t := by
    refine ⟨-(k' : ℤ), ?_⟩
    unfold knot
    rw [if_pos (by omega)]
    have : (2 : ℝ) ^ (-(k' : ℤ) - 1) ≤ (1 / 2) ^ k' := by
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  have hlt : t < knot (n + 1) := by
    by_contra h
    push Not at h
    have := hmax _ h
    omega
  rw [knot_succ] at hlt
  have hpos : (0 : ℝ) < 2 ^ ex n := by positivity
  set y : ℝ := n + (t - knot n) / 2 ^ ex n with hy
  have hfl : ⌊y⌋ = n := by
    rw [Int.floor_eq_iff]
    constructor
    · have : 0 ≤ (t - knot n) / 2 ^ ex n := div_nonneg (by linarith) hpos.le
      linarith
    · have : (t - knot n) / 2 ^ ex n < 1 := by rw [div_lt_one hpos]; linarith
      linarith
  refine ⟨y, ?_⟩
  unfold alpha
  rw [hfl, hy]
  field_simp
  ring

/-! ## Section 4: the dyadic affine group `Aff` -/
/-- `y ↦ 2ⁿ y + b` as an order isomorphism of `ℝ`. -/
noncomputable def affIso (n : ℤ) (b : ℝ) : ℝ ≃o ℝ :=
  (OrderIso.mulLeft₀ ((2 : ℝ) ^ n) (by positivity)).trans (OrderIso.addRight b)

@[simp] lemma affIso_apply (n : ℤ) (b y : ℝ) : affIso n b y = 2 ^ n * y + b := rfl

/-- A dyadic affine map `y ↦ 2ⁿ y + b`, `b` dyadic. -/
def IsDAffMap (f : ℝ ≃o ℝ) : Prop := ∃ (n : ℤ) (b : ℝ), IsDyadic b ∧ ∀ y, f y = 2 ^ n * y + b

/-- The dyadic affine group. -/
def Aff : Subgroup (ℝ ≃o ℝ) where
  carrier := {f | IsDAffMap f}
  mul_mem' := by
    rintro f g ⟨n, b, hb, hf⟩ ⟨m, b', hb', hg⟩
    refine ⟨n + m, 2 ^ n * b' + b, isDyadic_add (isDyadic_zpow_mul hb') hb, fun y => ?_⟩
    rw [RelIso.mul_apply, hg, hf, zpow_add₀ two_ne_zero]
    ring
  one_mem' := ⟨0, 0, isDyadic_zero, fun y => by simp [RelIso.one_apply]⟩
  inv_mem' := by
    rintro f ⟨n, b, hb, hf⟩
    refine ⟨-n, -(2 ^ (-n) * b), isDyadic_neg (isDyadic_zpow_mul hb), fun y => ?_⟩
    apply f.injective
    rw [RelIso.apply_inv_self, hf]
    have h2 : (2 : ℝ) ^ n * 2 ^ (-n) = 1 := by rw [← zpow_add₀ two_ne_zero]; simp
    linear_combination (b - y) * h2

lemma affIso_mem (n : ℤ) {b : ℝ} (hb : IsDyadic b) : affIso n b ∈ Aff :=
  ⟨n, b, hb, fun _ => rfl⟩

lemma slope_ne_zero (f : Aff) : (f : ℝ ≃o ℝ) 1 - (f : ℝ ≃o ℝ) 0 ≠ 0 := by
  obtain ⟨n, b, -, hf⟩ := f.2
  rw [hf, hf]
  simp only [mul_one, mul_zero, zero_add, add_sub_cancel_right]
  positivity

/-- The slope of a dyadic affine map, as a homomorphism to `ℝˣ`. -/
noncomputable def slope : Aff →* ℝˣ where
  toFun f := Units.mk0 ((f : ℝ ≃o ℝ) 1 - (f : ℝ ≃o ℝ) 0) (slope_ne_zero f)
  map_one' := by ext; simp [RelIso.one_apply]
  map_mul' f g := by
    obtain ⟨n, b, -, hf⟩ := f.2
    obtain ⟨m, b', -, hg⟩ := g.2
    ext
    simp only [Subgroup.coe_mul, RelIso.mul_apply, Units.val_mul, Units.val_mk0, hf, hg]
    ring

lemma eq_add_of_mem_ker {a : Aff} (ha : a ∈ slope.ker) :
    ∃ b : ℝ, ∀ y, (a : ℝ ≃o ℝ) y = y + b := by
  obtain ⟨n, b, -, hf⟩ := a.2
  have h1 : (a : ℝ ≃o ℝ) 1 - (a : ℝ ≃o ℝ) 0 = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.mp ha)
    simpa [slope] using this
  rw [hf, hf] at h1
  have h2 : (2 : ℝ) ^ n = 1 := by linarith
  exact ⟨b, fun y => by rw [hf, h2, one_mul]⟩

lemma isSolvable_Aff : Group.IsSolvable Aff := by
  have : Group.IsSolvable slope.ker := Group.isSolvable_of_comm fun a b => by
    obtain ⟨β, ha⟩ := eq_add_of_mem_ker a.2
    obtain ⟨β', hb⟩ := eq_add_of_mem_ker b.2
    apply Subtype.ext; apply Subtype.ext; ext y
    simp only [Subgroup.coe_mul, RelIso.mul_apply, ha, hb]
    ring
  exact Group.isSolvable_of_ker_le_range slope.ker.subtype slope (by simp)

lemma isDyadic_apply_zero (f : Aff) : IsDyadic ((f : ℝ ≃o ℝ) 0) := by
  obtain ⟨n, b, hb, hf⟩ := f.2
  rw [hf]; simpa using hb

lemma isDyadic_apply_one (f : Aff) : IsDyadic ((f : ℝ ≃o ℝ) 1) := by
  obtain ⟨n, b, hb, hf⟩ := f.2
  rw [hf, mul_one]; exact isDyadic_add (isDyadic_zpow n) hb

instance countable_Aff : Countable Aff := by
  have : Countable {x : ℝ // IsDyadic x} := countable_isDyadic.to_subtype
  refine Function.Injective.countable
    (f := fun f : Aff => ((⟨_, isDyadic_apply_zero f⟩ : {x : ℝ // IsDyadic x}),
      (⟨_, isDyadic_apply_one f⟩ : {x : ℝ // IsDyadic x}))) ?_
  intro f g hfg
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hfg
  obtain ⟨n, b, -, hf⟩ := f.2
  obtain ⟨m, b', -, hg⟩ := g.2
  rw [hf, hf, hg, hg] at hfg
  apply Subtype.ext; ext y
  rw [hf, hg]
  have hb : b = b' := by simpa using hfg.1
  have hn : (2 : ℝ) ^ n = 2 ^ m := by linarith [hfg.2]
  rw [hb, hn]

/-! ## Section 5: the conjugated action on `P¹` -/
/-- The data of the published conjugacy of `HRat` with Thompson's group `F`. -/
structure Conj where
  c : ℝ → ℝ
  mono : StrictMonoOn c (Set.Ioo 0 1)
  surj : c '' Set.Ioo 0 1 = Set.univ
  φ : Monod.HRat ≃* CannonFloydParry.F
  hφ : ∀ (h : Monod.HRat), ∀ t ∈ Set.Ioo (0 : ℝ) 1,
    (h : OnePoint ℝ ≃ₜ OnePoint ℝ) (c t : OnePoint ℝ) =
      (c (CannonFloydParry.extend (φ h : CannonFloydParry.UI ≃o CannonFloydParry.UI) t) :
        OnePoint ℝ)

lemma nonempty_conj : Nonempty Conj := by
  obtain ⟨-, c, hc, hcs, φ, hφ⟩ := Monod.contDiff_and_exists_mulEquiv_HRat_F
  exact ⟨⟨c, hc, hcs, φ, hφ⟩⟩

end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
namespace Conj
variable (K : Conj)
lemma exists_eq (r : ℝ) : ∃ t ∈ Set.Ioo (0 : ℝ) 1, K.c t = r := by
  have : r ∈ K.c '' Set.Ioo 0 1 := by rw [K.surj]; trivial
  exact this

lemma psi_strictMono : StrictMono (K.c ∘ alpha) := fun _ _ h =>
  K.mono (alpha_mem _) (alpha_mem _) (alpha_strictMono h)

lemma psi_surj : Function.Surjective (K.c ∘ alpha) := by
  intro r
  obtain ⟨t, ht, rfl⟩ := K.exists_eq r
  obtain ⟨y, rfl⟩ := alpha_surj ht
  exact ⟨y, rfl⟩

/-- `Psi = c ∘ alpha`, an order isomorphism of `ℝ`. -/
noncomputable def Psi : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ K.psi_strictMono K.psi_surj

lemma Psi_apply (y : ℝ) : K.Psi y = K.c (alpha y) := rfl

/-- Conjugation by `Psi`, then extension to `P¹`. -/
noncomputable def rho : (ℝ ≃o ℝ) →* Hom where
  toFun f := Homeomorph.onePointCongr (K.Psi.symm.trans (f.trans K.Psi)).toHomeomorph
  map_one' := by
    ext x
    induction x using OnePoint.rec <;> simp
  map_mul' f g := by
    ext x
    induction x using OnePoint.rec <;> simp

lemma rho_coe (f : ℝ ≃o ℝ) (z : ℝ) :
    K.rho f ((K.Psi z : ℝ) : OnePoint ℝ) = ((K.Psi (f z) : ℝ) : OnePoint ℝ) := by
  simp [rho]

/-- The dyadic affine group acting on `P¹` through `Psi`. -/
noncomputable def Lam : Subgroup Hom := Aff.map K.rho

instance countable_Lam : Countable K.Lam :=
  (K.rho.subgroupMap_surjective Aff).countable

lemma isAmenable_Lam : Garrido.IsAmenable K.Lam := by
  have : Group.IsSolvable Aff := isSolvable_Aff
  have : Group.IsSolvable K.Lam :=
    Group.isSolvable_of_surjective (K.rho.subgroupMap_surjective Aff)
  exact Garrido.isAmenable_of_isSolvable_of_finiteIndex (⊤ : Subgroup K.Lam) inferInstance

end Conj
end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
/-! ## Section 5b: `SL₂(ℚ)` is countable -/
lemma countable_SLQ : Countable SLQ := by
  have h1 : (ratSubring : Set ℝ) = Set.range (Rat.castHom ℝ) := by
    simp [ratSubring]
  have : Countable ratSubring := by
    have hc : (ratSubring : Set ℝ).Countable := h1 ▸ Set.countable_range _
    exact hc.to_subtype
  have : Countable (Matrix (Fin 2) (Fin 2) ratSubring) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ratSubring))
  exact inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ratSubring // A.det = 1})

/-! ## Section 6: the conull set `X1 = c '' (non-dyadic points)` -/
lemma volP1_singleton (x : OnePoint ℝ) : Monod.volP1 {x} = 0 := by
  unfold Monod.volP1
  rw [Measure.map_apply OnePoint.continuous_coe.measurable (measurableSet_singleton x)]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  exact OnePoint.coe_injective (ha.trans hb.symm)

instance : NullSingletonClass Monod.volP1 := ⟨volP1_singleton⟩

lemma volP1_countable {s : Set (OnePoint ℝ)} (hs : s.Countable) : Monod.volP1 s = 0 :=
  hs.measure_zero _

end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
namespace Conj
variable (K : Conj)
/-- The images under `c` of the non-dyadic points of `(0,1)`. -/
def X1 : Set (OnePoint ℝ) := {x | ∃ t, NonDyadic t ∧ x = ((K.c t : ℝ) : OnePoint ℝ)}

lemma compl_X1_subset :
    K.X1ᶜ ⊆ insert OnePoint.infty ((fun t => ((K.c t : ℝ) : OnePoint ℝ)) '' {t | IsDyadic t}) := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact Set.mem_insert _ _
  | coe r =>
    right
    obtain ⟨t, ht, rfl⟩ := K.exists_eq r
    refine ⟨t, ?_, rfl⟩
    by_contra hd
    exact hx ⟨t, ⟨ht.1, ht.2, hd⟩, rfl⟩

lemma countable_compl_X1 : K.X1ᶜ.Countable :=
  ((countable_isDyadic.image _).insert _).mono K.compl_X1_subset

lemma measurableSet_X1 : MeasurableSet K.X1 :=
  K.countable_compl_X1.measurableSet.of_compl

lemma volP1_compl_X1 : Monod.volP1 K.X1ᶜ = 0 := volP1_countable K.countable_compl_X1

/-! ## Section 7: on `X1` the two orbit relations agree -/
lemma HRat_apply_mem_X1 {g : Hom} (hg : g ∈ Monod.HRat) {x : OnePoint ℝ} (hx : x ∈ K.X1) :
    g x ∈ K.X1 := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨_, (F_apply_nonDyadic_daff (K.φ ⟨g, hg⟩).2 ht).1, K.hφ ⟨g, hg⟩ t ⟨ht.1, ht.2.1⟩⟩

lemma sat (p : OnePoint ℝ × OnePoint ℝ) (hp : p ∈ orbRel Monod.HRat) :
    (p.1 ∈ K.X1 ↔ p.2 ∈ K.X1) := by
  obtain ⟨g, hg, hgp⟩ := hp
  rw [← hgp, smul_def]
  refine ⟨K.HRat_apply_mem_X1 hg, fun h => ?_⟩
  have := K.HRat_apply_mem_X1 (inv_mem hg) h
  rwa [show g⁻¹ (g p.1) = p.1 from inv_smul_smul g p.1] at this

/-- The orbit relation of `Lam`. -/
def RL : Set (OnePoint ℝ × OnePoint ℝ) := {p | ∃ l : K.Lam, l • p.1 = p.2}

lemma agree {x : OnePoint ℝ} (hx : x ∈ K.X1) (y : OnePoint ℝ) :
    (x, y) ∈ K.RL ↔ (x, y) ∈ orbRel Monod.HRat := by
  obtain ⟨t, ht, rfl⟩ := hx
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.1⟩
  obtain ⟨z, rfl⟩ := alpha_surj ht'
  have hx : ((K.c (alpha z) : ℝ) : OnePoint ℝ) = ((K.Psi z : ℝ) : OnePoint ℝ) := rfl
  constructor
  · rintro ⟨⟨l, hl⟩, hly⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hl
    rw [Subgroup.smul_def, smul_def] at hly
    simp only at hly
    rw [hx, rho_coe] at hly
    obtain ⟨n, b, hb, haf⟩ := ha
    have hs_daff : DAff (alpha (a z)) (alpha z) :=
      daff_trans (daff_alpha _) (daff_trans ⟨n, b, hb, haf z⟩ (daff_symm (daff_alpha z)))
    have hs : NonDyadic (alpha (a z)) := ⟨(alpha_mem _).1, (alpha_mem _).2,
      fun hd => ht.2.2 (isDyadic_of_daff (daff_symm hs_daff) hd)⟩
    obtain ⟨g, hg, hgt⟩ := exists_F_of_daff hs ht hs_daff
    refine ⟨(K.φ.symm ⟨g, hg⟩ : Hom), (K.φ.symm ⟨g, hg⟩).2, ?_⟩
    rw [smul_def]
    simp only
    rw [K.hφ _ _ ht', MulEquiv.apply_symm_apply, ← hly]
    simp only
    rw [hgt]
    rfl
  · rintro ⟨g, hg, hgy⟩
    rw [smul_def] at hgy
    simp only at hgy
    have e := K.hφ ⟨g, hg⟩ _ ht'
    obtain ⟨hsN, hsD⟩ := F_apply_nonDyadic_daff (K.φ ⟨g, hg⟩).2 ht
    obtain ⟨w, hw⟩ := alpha_surj ⟨hsN.1, hsN.2.1⟩
    have hwz : DAff w z :=
      daff_trans (daff_symm (daff_alpha w)) (by rw [hw]; exact daff_trans hsD (daff_alpha z))
    obtain ⟨n, b, hb, hwz⟩ := hwz
    refine ⟨⟨K.rho (affIso n b), Subgroup.mem_map.mpr ⟨_, affIso_mem n hb, rfl⟩⟩, ?_⟩
    rw [Subgroup.smul_def, smul_def]
    simp only
    rw [hx, rho_coe, affIso_apply, ← hwz, Psi_apply, hw, ← hgy]
    exact e.symm

/-! ## Section 8: `Lam` preserves null sets -/
lemma null_preimage (l : K.Lam) {s : Set (OnePoint ℝ)} (hs : Monod.volP1 s = 0) :
    Monod.volP1 ((fun x => l • x) ⁻¹' s) = 0 := by
  have : Countable SLQ := countable_SLQ
  have hN : Monod.volP1 (K.X1 ∩ X0)ᶜ = 0 := by
    rw [Set.compl_inter]; exact measure_union_null K.volP1_compl_X1 volP1_compl_X0
  refine measure_mono_null (t := (K.X1 ∩ X0)ᶜ ∪ ⋃ g : SLQ, Monod.mob g ⁻¹' s) ?_
    (measure_union_null hN (measure_iUnion_null fun g => null_preimage_mob g hs))
  intro x hx
  by_cases hxX : x ∈ K.X1 ∩ X0
  · right
    obtain ⟨h, hh, hhx⟩ := (K.agree hxX.1 (l • x)).mp ⟨l, rfl⟩
    obtain ⟨g, hg⟩ := exists_mob_of_mem_HB (HRat_le_HB hh) hxX.2
    refine Set.mem_iUnion.mpr ⟨g, ?_⟩
    show Monod.mob g x ∈ s
    rw [← hg, ← smul_def]
    simp only at hhx
    rw [hhx]
    exact hx
  · left; exact hxX

end Conj
end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
/-! ## `volP1` is σ-finite -/
theorem sigmaFinite_volP1 : SigmaFinite Monod.volP1 := by
  unfold Monod.volP1
  exact (OnePoint.isOpenEmbedding_coe (X := ℝ)).measurableEmbedding.sigmaFinite_map

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
variable {X : Type*}
/-! ## Part E3: relations agreeing on a conull saturated set -/
/-- Cut a function on `X × X` down to the pairs with first coordinate in `X₁`. -/
noncomputable def cut (X₁ : Set X) (f : X × X → ℝ) : X × X → ℝ :=
  (Prod.fst ⁻¹' X₁).indicator f

theorem cut_of_mem {X₁ : Set X} (f : X × X → ℝ) {p : X × X} (hp : p.1 ∈ X₁) :
    cut X₁ f p = f p :=
  Set.indicator_of_mem (show p ∈ Prod.fst ⁻¹' X₁ from hp) f

theorem cut_of_notMem {X₁ : Set X} (f : X × X → ℝ) {p : X × X} (hp : p.1 ∉ X₁) :
    cut X₁ f p = 0 :=
  Set.indicator_of_notMem (show p ∉ Prod.fst ⁻¹' X₁ from hp) f

theorem isBddMeasOn_cut [MeasurableSpace X] {R R' : Set (X × X)} {X₁ : Set X} (hX₁ : MeasurableSet X₁)
    (hagree : ∀ x ∈ X₁, ∀ y, (x, y) ∈ R ↔ (x, y) ∈ R') {f : X × X → ℝ}
    (hf : Monod.IsBddMeasOn R' f) : Monod.IsBddMeasOn R (cut X₁ f) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm.indicator (measurable_fst hX₁), max C 0, fun p hp => ?_⟩
  by_cases h1 : p.1 ∈ X₁
  · rw [cut_of_mem f h1]
    exact (hC p ((hagree p.1 h1 p.2).1 hp)).trans (le_max_left _ _)
  · rw [cut_of_notMem f h1, abs_zero]
    exact le_max_right _ _

/-- A partial transformation of `R'`, restricted to `X₁`, is a partial transformation of `R`. -/
noncomputable def restrictPT [MeasurableSpace X] {R R' : Set (X × X)} {X₁ : Set X} (hX₁ : MeasurableSet X₁)
    (hsat : ∀ p ∈ R', (p.1 ∈ X₁ ↔ p.2 ∈ X₁))
    (hagree : ∀ x ∈ X₁, ∀ y, (x, y) ∈ R ↔ (x, y) ∈ R')
    (φ : Monod.PartialTransformation R') : Monod.PartialTransformation R where
  dom := φ.dom ∩ X₁
  cod := φ.cod ∩ X₁
  measurableSet_dom := φ.measurableSet_dom.inter hX₁
  measurableSet_cod := φ.measurableSet_cod.inter hX₁
  e :=
    { toFun := fun a => ⟨φ.e ⟨a, a.2.1⟩, (φ.e ⟨a, a.2.1⟩).2,
        (hsat _ (φ.graph_subset ⟨a, a.2.1⟩)).1 a.2.2⟩
      invFun := fun b => ⟨φ.e.symm ⟨b, b.2.1⟩, (φ.e.symm ⟨b, b.2.1⟩).2, by
        have := hsat _ (φ.graph_subset (φ.e.symm ⟨b, b.2.1⟩))
        simp only [MeasurableEquiv.apply_symm_apply] at this
        exact this.2 b.2.2⟩
      left_inv := fun a => by
        apply Subtype.ext
        simp
      right_inv := fun b => by
        apply Subtype.ext
        simp
      measurable_toFun := by
        refine Measurable.subtype_mk ?_
        exact measurable_subtype_coe.comp
          (φ.e.measurable.comp measurable_subtype_coe.subtype_mk)
      measurable_invFun := by
        refine Measurable.subtype_mk ?_
        exact measurable_subtype_coe.comp
          (φ.e.symm.measurable.comp measurable_subtype_coe.subtype_mk) }
  graph_subset a := (hagree _ a.2.2 _).2 (φ.graph_subset ⟨a, a.2.1⟩)

theorem shiftRel_restrictPT [MeasurableSpace X] {R R' : Set (X × X)} {X₁ : Set X} (hX₁ : MeasurableSet X₁)
    (hsat : ∀ p ∈ R', (p.1 ∈ X₁ ↔ p.2 ∈ X₁))
    (hagree : ∀ x ∈ X₁, ∀ y, (x, y) ∈ R ↔ (x, y) ∈ R')
    (φ : Monod.PartialTransformation R') (f : X × X → ℝ) :
    (restrictPT hX₁ hsat hagree φ).shiftRel (cut X₁ f) = cut X₁ (φ.shiftRel f) := by
  funext p
  by_cases h1 : p.1 ∈ X₁
  · rw [cut_of_mem _ h1]
    by_cases h2 : p.1 ∈ φ.cod
    · have h12 : p.1 ∈ (restrictPT hX₁ hsat hagree φ).cod := ⟨h2, h1⟩
      simp only [Monod.PartialTransformation.shiftRel, dif_pos h12, dif_pos h2]
      have hmem := ((restrictPT hX₁ hsat hagree φ).e.symm ⟨p.1, h12⟩).2.2
      rw [cut_of_mem _ hmem]
      rfl
    · have h12 : p.1 ∉ (restrictPT hX₁ hsat hagree φ).cod := fun h => h2 h.1
      simp only [Monod.PartialTransformation.shiftRel, dif_neg h12, dif_neg h2]
  · rw [cut_of_notMem _ h1]
    have h12 : p.1 ∉ (restrictPT hX₁ hsat hagree φ).cod := fun h => h1 h.2
    simp only [Monod.PartialTransformation.shiftRel, dif_neg h12]

theorem shiftBase_restrictPT [MeasurableSpace X] {R R' : Set (X × X)} {X₁ : Set X} (hX₁ : MeasurableSet X₁)
    (hsat : ∀ p ∈ R', (p.1 ∈ X₁ ↔ p.2 ∈ X₁))
    (hagree : ∀ x ∈ X₁, ∀ y, (x, y) ∈ R ↔ (x, y) ∈ R')
    (φ : Monod.PartialTransformation R') (F : X → ℝ) {y : X} (hy : y ∈ X₁) :
    (restrictPT hX₁ hsat hagree φ).shiftBase F y = φ.shiftBase F y := by
  by_cases h2 : y ∈ φ.cod
  · have h12 : y ∈ (restrictPT hX₁ hsat hagree φ).cod := ⟨h2, hy⟩
    simp only [Monod.PartialTransformation.shiftBase, dif_pos h12, dif_pos h2]
    rfl
  · have h12 : y ∉ (restrictPT hX₁ hsat hagree φ).cod := fun h => h2 h.1
    simp only [Monod.PartialTransformation.shiftBase, dif_neg h12, dif_neg h2]

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
theorem isAmenableRel_of_agree {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {R R' : Set (X × X)} (X₁ : Set X) (hX₁ : MeasurableSet X₁) (hX₁c : μ X₁ᶜ = 0)
    (hsat : ∀ p ∈ R', (p.1 ∈ X₁ ↔ p.2 ∈ X₁))
    (hagree : ∀ x ∈ X₁, ∀ y, (x, y) ∈ R ↔ (x, y) ∈ R')
    (h : Monod.IsAmenableRel μ R) : Monod.IsAmenableRel μ R' := by
  obtain ⟨P, hP⟩ := h
  have hae : ∀ᵐ y ∂μ, y ∈ X₁ := ae_iff.2 hX₁c
  have hbdd : ∀ f, Monod.IsBddMeasOn R' f → Monod.IsBddMeasOn R (cut X₁ f) :=
    fun f hf => isBddMeasOn_cut hX₁ hagree hf
  refine ⟨fun f => P (cut X₁ f), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro f hf
    exact hP.aemeasurable _ (hbdd f hf)
  · intro f g hf hg hfg
    refine hP.congr _ _ (hbdd f hf) (hbdd g hg) ?_
    unfold Monod.RelNull at hfg ⊢
    refine measure_mono_null ?_ hfg
    rintro x ⟨p, ⟨hp, hpR⟩, rfl⟩
    by_cases h1 : p.1 ∈ X₁
    · refine ⟨p, ⟨?_, (hagree p.1 h1 p.2).1 hpR⟩, rfl⟩
      have hp' : cut X₁ f p ≠ cut X₁ g p := hp
      rwa [cut_of_mem _ h1, cut_of_mem _ h1] at hp'
    · exact absurd (by rw [cut_of_notMem _ h1, cut_of_notMem _ h1]) hp
  · intro f g hf hg
    have : cut X₁ (f + g) = cut X₁ f + cut X₁ g := Set.indicator_add _ _ _
    show P (cut X₁ (f + g)) =ᵐ[μ] P (cut X₁ f) + P (cut X₁ g)
    rw [this]
    exact hP.add _ _ (hbdd f hf) (hbdd g hg)
  · intro c f hf
    have : cut X₁ (c • f) = c • cut X₁ f := by
      funext p
      by_cases h1 : p.1 ∈ X₁
      · rw [Pi.smul_apply, cut_of_mem _ h1, cut_of_mem _ h1]
        rfl
      · rw [Pi.smul_apply, cut_of_notMem _ h1, cut_of_notMem _ h1, smul_zero]
    show P (cut X₁ (c • f)) =ᵐ[μ] c • P (cut X₁ f)
    rw [this]
    exact hP.smul _ _ (hbdd f hf)
  · intro f hf hpos
    refine hP.nonneg _ (hbdd f hf) fun p hp => ?_
    by_cases h1 : p.1 ∈ X₁
    · rw [cut_of_mem _ h1]
      exact hpos p ((hagree p.1 h1 p.2).1 hp)
    · rw [cut_of_notMem _ h1]
  · have h1R : Monod.IsBddMeasOn R (1 : X × X → ℝ) :=
      ⟨measurable_const, 1, fun p _ => by simp⟩
    have h1R' : Monod.IsBddMeasOn R' (1 : X × X → ℝ) :=
      ⟨measurable_const, 1, fun p _ => by simp⟩
    show P (cut X₁ 1) =ᵐ[μ] 1
    refine (hP.congr _ _ (hbdd 1 h1R') h1R ?_).trans hP.one
    unfold Monod.RelNull
    refine measure_mono_null ?_ hX₁c
    rintro x ⟨p, ⟨hp, -⟩, rfl⟩ h1
    exact hp (cut_of_mem _ h1)
  · intro φ f hf
    show P (cut X₁ (φ.shiftRel f)) =ᵐ[μ] φ.shiftBase (P (cut X₁ f))
    rw [← shiftRel_restrictPT hX₁ hsat hagree φ f]
    refine (hP.invariant (restrictPT hX₁ hsat hagree φ) _ (hbdd f hf)).trans ?_
    exact hae.mono fun y hy => shiftBase_restrictPT hX₁ hsat hagree φ _ hy

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part E3: amenability passes between relations that agree on a conull saturated set -/
alias isAmenableRel_of_agree := ThompsonAmenability.M51.PartA.isAmenableRel_of_agree

/-! ## Assembly -/
alias sigmaFinite_volP1 := ThompsonAmenability.M51.PartA.sigmaFinite_volP1

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
/-! ## Section 9: assembly -/
theorem isAmenableRel_HRat : Monod.IsAmenableRel Monod.volP1 (orbRel Monod.HRat) := by
  obtain ⟨K⟩ := nonempty_conj
  have := sigmaFinite_volP1
  have hL : Monod.IsAmenableRel Monod.volP1 K.RL :=
    Monod.isAmenableRel_orbit_of_isAmenable Monod.volP1 K.Lam
      (fun l => (l : Hom).continuous.measurable) (fun l s hs => K.null_preimage l hs)
      K.isAmenable_Lam
  exact isAmenableRel_of_agree Monod.volP1 K.X1 K.measurableSet_X1 K.volP1_compl_X1 K.sat
    (fun x hx y => K.agree hx y) hL

end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part E2: the orbit relation of `H_ℚ(ℤ)` is amenable -/

end ThompsonAmenability.M51
end

end
end

section
section
namespace ThompsonOrbit

theorem isAmenableRel_orbit_HRat :
    Monod.IsAmenableRel Monod.volP1
      {p : OnePoint ℝ × OnePoint ℝ | ∃ g ∈ Monod.HRat, g p.1 = p.2} :=
  ThompsonAmenability.M51.PartE2.isAmenableRel_HRat

end ThompsonOrbit

end
end

section
open ThompsonOrbit

theorem solution :
    Monod.IsAmenableRel Monod.volP1
      {p : OnePoint ℝ × OnePoint ℝ | ∃ g ∈ Monod.HRat, g p.1 = p.2} := by
  apply ThompsonOrbit.isAmenableRel_orbit_HRat <;> assumption

end
