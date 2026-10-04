-- Prove2me | solution 1 for ThompsonAmenability.not_isCoamenable_HRat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T06:51:55.616663+00:00
-- url     : https://prove2.me/submissions/04120458-659e-4b4a-ba42-788f666b1c5a

import Mathlib
import Definitions.Def_ThompsonAmenability
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_CannonFloydParry
import Theorems.Thm_Monod_contDiff_and_exists_mulEquiv_HRat_F
import Theorems.Thm_Monod_not_isAmenableRel_mob
import Theorems.Thm_ThompsonOrbit_isAmenableRel_orbit_HRat

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

/-- The orbit relation of `SL₂(ℚ)` on `P¹`. -/
def RQ : Set (OnePoint ℝ × OnePoint ℝ) := {p | ∃ g : SLQ, Monod.mob g p.1 = p.2}

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
theorem HC1_le_HB : HC1RatRat ≤ HB ratSubring Monod.ratPoints := by
  unfold HC1RatRat
  rw [Subgroup.closure_le]
  rintro f ⟨hf, -⟩
  exact hf

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
alias HC1_le_HB := ThompsonAmenability.M51.PartA.HC1_le_HB

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
theorem HRat_le_HC1 : Monod.HRat ≤ HC1RatRat := by
  intro h hh
  apply Subgroup.subset_closure
  refine ⟨PartA.HRat_le_HB hh, ?_⟩
  obtain ⟨u, hu, hhu⟩ := Monod.contDiff_and_exists_mulEquiv_HRat_F.1 h hh
  obtain ⟨v, hv, hhv⟩ := Monod.contDiff_and_exists_mulEquiv_HRat_F.1 h⁻¹ (inv_mem hh)
  refine ⟨u, hu, fun x => ?_, hhu⟩
  have hvu : ∀ y, v (u y) = y := by
    intro y
    have h1 : (h⁻¹ : OnePoint ℝ ≃ₜ OnePoint ℝ) (h (y : OnePoint ℝ)) = y := by
      rw [Homeomorph.inv_apply]
      exact h.symm_apply_apply _
    rw [hhu, hhv] at h1
    exact OnePoint.coe_injective h1
  have hcomp : v ∘ u = id := funext hvu
  have hud : DifferentiableAt ℝ u x := (hu.differentiable one_ne_zero) x
  have hvd : DifferentiableAt ℝ v (u x) := (hv.differentiable one_ne_zero) (u x)
  have hd := hvd.hasDerivAt.comp x hud.hasDerivAt
  rw [hcomp] at hd
  have h1 := hd.unique (hasDerivAt_id x)
  intro h0
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
alias HRat_le_HC1 := ThompsonAmenability.M51.PartA.HRat_le_HC1

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
/-! ## The subring `ℚ` -/
theorem coe_ratSubring : (ratSubring : Set ℝ) = Set.range ((↑) : ℚ → ℝ) := by
  rw [ratSubring, RingHom.coe_range]
  rfl

theorem countable_ratSubring : Countable ratSubring := by
  have h : (ratSubring : Set ℝ).Countable := by
    rw [coe_ratSubring]
    exact Set.countable_range _
  exact h.to_subtype

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
alias countable_ratSubring := ThompsonAmenability.M51.PartA.countable_ratSubring

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
theorem dense_ratSubring : Dense (ratSubring : Set ℝ) := by
  rw [coe_ratSubring]
  exact Rat.denseRange_cast

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
alias dense_ratSubring := ThompsonAmenability.M51.PartA.dense_ratSubring

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

theorem measurableSet_X0 : MeasurableSet X0 := by
  exact countable_compl_X0.measurableSet.of_compl

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part B: elements of `H_ℚ(ℚ)` at irrational points -/
alias measurableSet_X0 := ThompsonAmenability.M51.PartB.measurableSet_X0

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
alias mob_mem_X0_iff := ThompsonAmenability.M51.PartB.mob_mem_X0_iff

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

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
theorem null_preimage_of_mem_HB {h : Hom} (hh : h ∈ HB ratSubring Monod.ratPoints)
    {s : Set (OnePoint ℝ)} (hs : Monod.volP1 s = 0) : Monod.volP1 (h ⁻¹' s) = 0 := by
  have hsub : (h : OnePoint ℝ → OnePoint ℝ) ⁻¹' s ⊆ X0ᶜ ∪ ⋃ g : SLQ, Monod.mob g ⁻¹' s := by
    intro x hx
    by_cases hx0 : x ∈ X0
    · obtain ⟨g, hg⟩ := exists_mob_of_mem_HB hh hx0
      refine Or.inr (mem_iUnion.2 ⟨g, ?_⟩)
      show Monod.mob g x ∈ s
      rw [← hg]; exact hx
    · exact Or.inl hx0
  exact measure_mono_null hsub (measure_union_null volP1_compl_X0
    (measure_iUnion_null fun g => null_preimage_mob g hs))

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
alias null_preimage_of_mem_HB := ThompsonAmenability.M51.PartB.null_preimage_of_mem_HB

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
/-- The real entries of a matrix over a subring of `ℝ`. -/
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

lemma mob_map_inclusion {A B : Subring ℝ} (h : A ≤ B) (g : Matrix.SpecialLinearGroup (Fin 2) A)
    (x : OnePoint ℝ) :
    Monod.mob (Matrix.SpecialLinearGroup.map (Subring.inclusion h) g) x = Monod.mob g x := by
  cases x with
  | infty => rw [mob_infty, mob_infty]; rfl
  | coe t => rw [mob_coe, mob_coe]; rfl

lemma isPiecewiseProjOn_mono {A A' : Subring ℝ} (hA : A ≤ A') {E E' : Set (OnePoint ℝ)}
    (hE : E ⊆ E') {f : Hom} (h : Monod.IsPiecewiseProjOn A E f) :
    Monod.IsPiecewiseProjOn A' E' f := by
  obtain ⟨B, hB, hloc⟩ := h
  refine ⟨B, hB.trans hE, fun x hx => ?_⟩
  obtain ⟨g, hg⟩ := hloc x hx
  exact ⟨Matrix.SpecialLinearGroup.map (Subring.inclusion hA) g,
    hg.mono fun y hy => by rw [hy, mob_map_inclusion]⟩

/-- An integer matrix in `SL(2, A)`. -/
def mkSL (A : Subring ℝ) (a b c d : ℤ) (h : a * d - b * c = 1) :
    Matrix.SpecialLinearGroup (Fin 2) A :=
  ⟨!![(a : A), b; c, d], by
    rw [Matrix.det_fin_two_of]
    exact_mod_cast congrArg (fun z : ℤ => (z : A)) h⟩

lemma mob_mkSL_coe (a b c d : ℤ) (h : a * d - b * c = 1) (t : ℝ) :
    Monod.mob (mkSL A a b c d h) (t : OnePoint ℝ) = if (c : ℝ) * t + d = 0 then ∞ else
      ((((a : ℝ) * t + b) / ((c : ℝ) * t + d) : ℝ) : OnePoint ℝ) := by
  rw [mob_coe]
  have e00 : ent (mkSL A a b c d h) 0 0 = a := by simp [ent, mkSL]
  have e01 : ent (mkSL A a b c d h) 0 1 = b := by simp [ent, mkSL]
  have e10 : ent (mkSL A a b c d h) 1 0 = c := by simp [ent, mkSL]
  have e11 : ent (mkSL A a b c d h) 1 1 = d := by simp [ent, mkSL]
  rw [e00, e01, e10, e11]

/-! ### Order automorphisms of `ℝ`, extended to `P¹` -/
/-- An order automorphism of `ℝ`, extended to `P¹` fixing `∞`. -/
noncomputable def liftO (e : ℝ ≃o ℝ) : Hom := e.toHomeomorph.onePointCongr

/-! ### The element `hS` -/
/-- `y - 2` on `(-∞, 1]`, `-1/y` on `[1, 2]`, `(y - 3)/(4 - y)` on `[2, 3]`, `y - 3` on `[3, ∞)`. -/
noncomputable def psi (t : ℝ) : ℝ :=
  if t ≤ 1 then t - 2 else if t ≤ 2 then -1 / t else if t ≤ 3 then (t - 3) / (4 - t) else t - 3

lemma psi_strictMono : StrictMono psi := by
  intro x y hxy
  simp only [psi]
  split_ifs <;> first
    | linarith
    | (rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith)
    | (rw [lt_div_iff₀ (by linarith)]; nlinarith)
    | (rw [div_lt_iff₀ (by linarith)]; nlinarith)

/-- The inverse of `psi`. -/
noncomputable def phi (z : ℝ) : ℝ :=
  if z ≤ -1 then z + 2 else if z ≤ -1 / 2 then -1 / z else if z ≤ 0 then (4 * z + 3) / (z + 1)
  else z + 3

lemma psi_phi (z : ℝ) : psi (phi z) = z := by
  unfold phi
  split_ifs with h1 h2 h3
  · rw [psi, if_pos (by linarith)]; ring
  · have hz : z < 0 := by linarith
    have hge : 1 < -1 / z := by rw [lt_div_iff_of_neg hz]; linarith
    have hle : -1 / z ≤ 2 := by rw [div_le_iff_of_neg hz]; linarith
    rw [psi, if_neg (by linarith), if_pos hle]
    field_simp
  · have hz : 0 < z + 1 := by linarith
    have hge : 2 < (4 * z + 3) / (z + 1) := by rw [lt_div_iff₀ hz]; linarith
    have hle : (4 * z + 3) / (z + 1) ≤ 3 := by rw [div_le_iff₀ hz]; linarith
    rw [psi, if_neg (by linarith), if_neg (by linarith), if_pos hle]
    have e1 : (4 * z + 3) / (z + 1) - 3 = z / (z + 1) := by field_simp; ring
    have e2 : 4 - (4 * z + 3) / (z + 1) = 1 / (z + 1) := by field_simp; ring
    rw [e1, e2]
    field_simp
  · rw [psi, if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]; ring

/-- `psi` as an order automorphism of `ℝ`. -/
noncomputable def psiO : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective psi psi_strictMono (fun z => ⟨phi z, psi_phi z⟩)

/-- The element `h_S` of `H_ℚ(ℤ)`: equal to `y ↦ -1/y` on `[1, 2]`. -/
noncomputable def hS : Hom := liftO psiO

lemma hS_coe (t : ℝ) : hS (t : OnePoint ℝ) = ((psi t : ℝ) : OnePoint ℝ) := rfl

lemma hS_coe_of_mem {t : ℝ} (h1 : 1 < t) (h2 : t ≤ 2) :
    hS (t : OnePoint ℝ) = ((-t⁻¹ : ℝ) : OnePoint ℝ) := by
  rw [hS_coe, psi, if_neg (by linarith), if_pos h2, neg_div, one_div]

lemma hS_pw (A : Subring ℝ) : Monod.IsPiecewiseProjOn A Monod.ratPoints hS := by
  classical
  refine ⟨{((1 : ℝ) : OnePoint ℝ), ((2 : ℝ) : OnePoint ℝ), ((3 : ℝ) : OnePoint ℝ), ∞}, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨1, by norm_num⟩
    · exact Or.inr ⟨2, by norm_num⟩
    · exact Or.inr ⟨3, by norm_num⟩
    · exact Or.inl rfl
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    obtain ⟨h1, h2, h3, h4⟩ := hx
    cases x with
    | infty => exact absurd rfl h4
    | coe t =>
      have h1' : t ≠ 1 := fun h => h1 (by rw [h])
      have h2' : t ≠ 2 := fun h => h2 (by rw [h])
      have h3' : t ≠ 3 := fun h => h3 (by rw [h])
      rcases lt_or_gt_of_ne h1' with ht1 | ht1
      · refine ⟨mkSL A 1 (-2) 0 1 (by norm_num), ?_⟩
        rw [OnePoint.nhds_coe_eq, eventually_map]
        filter_upwards [Iio_mem_nhds ht1] with s hs
        rw [hS_coe, mob_mkSL_coe, if_neg (by push_cast; norm_num), psi, if_pos (le_of_lt hs)]
        push_cast
        congr 1
        ring
      rcases lt_or_gt_of_ne h2' with ht2 | ht2
      · refine ⟨mkSL A 0 (-1) 1 0 (by norm_num), ?_⟩
        rw [OnePoint.nhds_coe_eq, eventually_map]
        filter_upwards [Ioo_mem_nhds ht1 ht2] with s hs
        rw [hS_coe, mob_mkSL_coe, if_neg (by push_cast; linarith [hs.1]), psi,
          if_neg (by linarith [hs.1]), if_pos hs.2.le]
        push_cast
        congr 1
        ring
      rcases lt_or_gt_of_ne h3' with ht3 | ht3
      · refine ⟨mkSL A 1 (-3) (-1) 4 (by norm_num), ?_⟩
        rw [OnePoint.nhds_coe_eq, eventually_map]
        filter_upwards [Ioo_mem_nhds ht2 ht3] with s hs
        rw [hS_coe, mob_mkSL_coe, if_neg (by push_cast; linarith [hs.2]), psi,
          if_neg (by linarith [hs.1]), if_neg (by linarith [hs.1]), if_pos hs.2.le]
        push_cast
        congr 1
        ring
      · refine ⟨mkSL A 1 (-3) 0 1 (by norm_num), ?_⟩
        rw [OnePoint.nhds_coe_eq, eventually_map]
        filter_upwards [Ioi_mem_nhds ht3] with s hs
        have hs' : 3 < s := hs
        rw [hS_coe, mob_mkSL_coe, if_neg (by push_cast; norm_num), psi,
          if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
        push_cast
        congr 1
        ring

lemma hS_mem_HRat : hS ∈ Monod.HRat := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.subset_closure ⟨Subgroup.subset_closure
    (isPiecewiseProjOn_mono le_top (subset_univ _) (hS_pw ⊥)), hS_pw ⊥⟩, rfl⟩

lemma hS_mem : hS ∈ HC1RatRat := HRat_le_HC1 hS_mem_HRat

/-! ### The rational affine maps -/
/-- A rational number as an element of the subring `ℚ` of `ℝ`. -/
noncomputable def ratElt (q : ℚ) : ratSubring := ⟨(q : ℝ), RingHom.mem_range.2 ⟨q, by simp⟩⟩

/-- `t ↦ a² t + a b`, an order automorphism of `ℝ` for `a ≠ 0`. -/
noncomputable def affO (a b : ℚ) (ha : a ≠ 0) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (fun t : ℝ => (a : ℝ) ^ 2 * t + a * b)
    (fun s t hst => by
      have : (0 : ℝ) < (a : ℝ) ^ 2 := by positivity
      simp only
      nlinarith)
    (fun z => ⟨(z - a * b) / (a : ℝ) ^ 2, by
      have : (a : ℝ) ≠ 0 := by exact_mod_cast ha
      simp only
      field_simp
      ring⟩)

/-- The rational affine map `t ↦ a² t + a b` of `P¹`. -/
noncomputable def aff (a b : ℚ) (ha : a ≠ 0) : Hom := liftO (affO a b ha)

lemma aff_coe (a b : ℚ) (ha : a ≠ 0) (t : ℝ) :
    aff a b ha (t : OnePoint ℝ) = (((a : ℝ) ^ 2 * t + a * b : ℝ) : OnePoint ℝ) := rfl

/-- The matrix `!![a, b; 0, a⁻¹] ∈ SL₂(ℚ)`. -/
noncomputable def affSL (a b : ℚ) (ha : a ≠ 0) : SLQ :=
  ⟨!![ratElt a, ratElt b; 0, ratElt a⁻¹], by
    rw [Matrix.det_fin_two_of]
    apply Subtype.ext
    simp [ratElt, ha]⟩

lemma aff_eq_mob (a b : ℚ) (ha : a ≠ 0) (x : OnePoint ℝ) :
    aff a b ha x = Monod.mob (affSL a b ha) x := by
  have e00 : ent (affSL a b ha) 0 0 = a := by simp [ent, affSL, ratElt]
  have e01 : ent (affSL a b ha) 0 1 = b := by simp [ent, affSL, ratElt]
  have e10 : ent (affSL a b ha) 1 0 = 0 := by simp [ent, affSL, ratElt]
  have e11 : ent (affSL a b ha) 1 1 = (a : ℝ)⁻¹ := by simp [ent, affSL, ratElt]
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  cases x with
  | infty => rw [mob_infty, e10, if_pos rfl]; rfl
  | coe t =>
    rw [aff_coe, mob_coe, e00, e01, e10, e11, if_neg (by simpa using ha')]
    congr 1
    field_simp
    ring

lemma aff_mem (a b : ℚ) (ha : a ≠ 0) : aff a b ha ∈ HC1RatRat := by
  apply Subgroup.subset_closure
  have hpw : Monod.IsPiecewiseProjOn ratSubring Monod.ratPoints (aff a b ha) :=
    ⟨∅, by simp, fun x _ => ⟨affSL a b ha, Eventually.of_forall fun y => aff_eq_mob a b ha y⟩⟩
  refine ⟨Subgroup.mem_inf.2 ⟨Subgroup.subset_closure ⟨Subgroup.subset_closure
    (isPiecewiseProjOn_mono le_top (subset_univ _) hpw), hpw⟩, rfl⟩,
    fun t => (a : ℝ) ^ 2 * t + a * b, by fun_prop, fun t => ?_, fun t => rfl⟩
  have hd : HasDerivAt (fun t : ℝ => (a : ℝ) ^ 2 * t + a * b) ((a : ℝ) ^ 2) t := by
    simpa using ((hasDerivAt_id t).const_mul ((a : ℝ) ^ 2)).add_const ((a : ℝ) * b)
  rw [hd.deriv]
  have : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  positivity

/-! ### The countable subgroup `CC` -/
/-- The generators: `hS` and the rational affine maps. -/
noncomputable def gens : Set Hom :=
  insert hS (range fun p : {a : ℚ // a ≠ 0} × ℚ => aff p.1 p.2 p.1.2)

/-- The subgroup generated by `hS` and the rational affine maps. -/
noncomputable def CC : Subgroup Hom := Subgroup.closure gens

lemma countable_CC : (CC : Set Hom).Countable := by
  have : Countable gens := ((Set.countable_range _).insert hS).to_subtype
  rw [CC, FreeGroup.closure_eq_range, MonoidHom.coe_range]
  exact Set.countable_range _

lemma CC_le : CC ≤ HC1RatRat := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro f (rfl | ⟨⟨⟨a, ha⟩, b⟩, rfl⟩)
  · exact hS_mem
  · exact aff_mem a b ha

lemma hS_mem_CC : hS ∈ CC := Subgroup.subset_closure (mem_insert _ _)

lemma aff_mem_CC (a b : ℚ) (ha : a ≠ 0) : aff a b ha ∈ CC :=
  Subgroup.subset_closure (mem_insert_of_mem _ ⟨(⟨a, ha⟩, b), rfl⟩)

/-! ### Realising `y ↦ -1/y` -/
lemma realize_S_pos {y : ℝ} (hy : 0 < y) : ∃ k ∈ CC, k (y : OnePoint ℝ) = ((-y⁻¹ : ℝ) : OnePoint ℝ) := by
  have hlt : Real.sqrt (1 / y) < Real.sqrt (2 / y) :=
    Real.sqrt_lt_sqrt (by positivity) (by gcongr; norm_num)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (Real.sqrt_nonneg _) hq1
  have hq : q ≠ 0 := by exact_mod_cast hq0.ne'
  have hsq1 : 1 / y < (q : ℝ) ^ 2 := (Real.sqrt_lt' hq0).1 hq1
  have hsq2 : (q : ℝ) ^ 2 < 2 / y := (Real.lt_sqrt hq0.le).1 hq2
  have hI1 : 1 < (q : ℝ) ^ 2 * y := by rwa [div_lt_iff₀ hy] at hsq1
  have hI2 : (q : ℝ) ^ 2 * y ≤ 2 := by rw [lt_div_iff₀ hy] at hsq2; linarith
  refine ⟨aff q 0 hq * hS * aff q 0 hq, CC.mul_mem (CC.mul_mem (aff_mem_CC _ _ _) hS_mem_CC)
    (aff_mem_CC _ _ _), ?_⟩
  rw [Homeomorph.mul_apply, Homeomorph.mul_apply, aff_coe]
  push_cast
  rw [mul_zero, add_zero, hS_coe_of_mem hI1 hI2, aff_coe]
  push_cast
  congr 1
  field_simp
  ring

lemma realize_S {y : ℝ} (hy : y ≠ 0) :
    ∃ k ∈ CC, k (y : OnePoint ℝ) = ((-y⁻¹ : ℝ) : OnePoint ℝ) := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have hy' : 0 < -y⁻¹ := by
      have := inv_lt_zero.2 hneg
      linarith
    obtain ⟨k, hk, hkx⟩ := realize_S_pos hy'
    refine ⟨k⁻¹, CC.inv_mem hk, ?_⟩
    rw [inv_neg, inv_inv, neg_neg] at hkx
    rw [Homeomorph.inv_apply, Homeomorph.symm_apply_eq, hkx]
  · exact realize_S_pos hpos

/-! ### Every `g ∈ SL₂(ℚ)` at every irrational point -/
lemma ent_rat (g : SLQ) (i j : Fin 2) : ∃ q : ℚ, ent g i j = q := by
  obtain ⟨q, hq⟩ := RingHom.mem_range.1 (g i j).2
  exact ⟨q, by simp [ent, ← hq]⟩

theorem exists_countable_cut :
    ∃ C : Set Hom, C.Countable ∧ C ⊆ HC1RatRat ∧
      ∀ x ∈ X0, ∀ g : SLQ, ∃ h ∈ C, h x = Monod.mob g x := by
  refine ⟨CC, countable_CC, CC_le, ?_⟩
  rintro x ⟨r, hr, rfl⟩ g
  obtain ⟨qa, ha⟩ := ent_rat g 0 0
  obtain ⟨qb, hb⟩ := ent_rat g 0 1
  obtain ⟨qc, hc⟩ := ent_rat g 1 0
  obtain ⟨qd, hd⟩ := ent_rat g 1 1
  have hdet := det_ent g
  rw [ha, hb, hc, hd] at hdet
  rw [mob_coe, ha, hb, hc, hd]
  by_cases hc0 : qc = 0
  · subst hc0
    have hqa : qa ≠ 0 := by rintro rfl; simp at hdet
    have hqd : (qd : ℝ) ≠ 0 := by intro h; rw [h] at hdet; simp at hdet
    have hqd' : (qd : ℝ) = (qa : ℝ)⁻¹ := eq_inv_of_mul_eq_one_right (by simpa using hdet)
    refine ⟨aff qa qb hqa, aff_mem_CC qa qb hqa, ?_⟩
    rw [aff_coe, if_neg (by simpa using hqd)]
    congr 1
    push_cast
    rw [hqd', zero_mul, zero_add, div_inv_eq_mul]
    ring
  · have hne : (qc : ℝ) * r + qd ≠ 0 := ((hr.ratCast_mul hc0).add_ratCast qd).ne_zero
    have hc0' : (qc : ℝ) ≠ 0 := by exact_mod_cast hc0
    obtain ⟨k, hk, hkx⟩ := realize_S (mul_ne_zero hc0' hne)
    refine ⟨aff 1 (qa / qc) one_ne_zero * k * aff qc qd hc0,
      CC.mul_mem (CC.mul_mem (aff_mem_CC _ _ _) hk) (aff_mem_CC _ _ _), ?_⟩
    rw [Homeomorph.mul_apply, Homeomorph.mul_apply, aff_coe]
    have e : (qc : ℝ) ^ 2 * r + qc * qd = qc * (qc * r + qd) := by ring
    rw [e, hkx, aff_coe, if_neg hne]
    congr 1
    push_cast
    field_simp
    linear_combination hdet

end ThompsonAmenability.M51.PartC
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part C: cut-and-paste -/
alias exists_countable_cut := ThompsonAmenability.M51.PartC.exists_countable_cut

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
/-- Finite additivity over the fibres of a map. -/
theorem mean_fam_fiber (hm : IsFinitelyAdditiveMeasure m) {α : Type*} [DecidableEq α]
    (π : X → α) (T : Finset α) :
    m (π ⁻¹' (T : Set α)) = ∑ a ∈ T, m (π ⁻¹' {a}) := by
  induction T using Finset.induction_on with
  | empty => simp [hm.1]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.coe_insert, Set.insert_eq, Set.preimage_union]
    apply hm.2
    exact Disjoint.preimage π (Set.disjoint_singleton_left.2 (by simpa using ha))

theorem mean_mono (hm : IsFinitelyAdditiveMeasure m) {s t : Set X} (h : s ⊆ t) : m s ≤ m t := by
  have : t = s ∪ (t \ s) := (Set.union_sdiff_cancel h).symm
  rw [this, hm.2 _ _ Set.disjoint_sdiff_right]
  exact le_self_add

theorem mean_ne_top (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : Set X) :
    m s ≠ ∞ :=
  ne_top_of_le_ne_top (by rw [h1]; exact ENNReal.one_ne_top) (mean_mono m hm (subset_univ s))

/-- The integral of a finitely valued function. -/
noncomputable def meanI (s : X → ℝ) : ℝ := ∑ᶠ v : ℝ, v * (m (s ⁻¹' {v})).toReal

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
theorem meanI_factor (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    {α : Type*} [DecidableEq α] (π : X → α) (T : Finset α) (hT : ∀ x, π x ∈ T) (ψ : α → ℝ) :
    meanI m (ψ ∘ π) = ∑ a ∈ T, ψ a * (m (π ⁻¹' {a})).toReal := by
  classical
  rw [meanI, finsum_eq_sum_of_support_subset _ (s := T.image ψ) ?_]
  · have e : ∀ v, (ψ ∘ π) ⁻¹' {v} = π ⁻¹' ((T.filter (fun a => ψ a = v) : Finset α) : Set α) := by
      intro v; ext x; simp [hT x]
    simp_rw [e, mean_fam_fiber m hm, ENNReal.toReal_sum (fun a _ => mean_ne_top m hm h1 _),
      Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (g := ψ) (t := T.image ψ)
      (fun a ha => Finset.mem_image_of_mem ψ ha)]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  · intro v hv
    rw [Function.mem_support] at hv
    by_contra h
    apply hv
    have : (ψ ∘ π) ⁻¹' {v} = ∅ := by
      ext x
      simp only [mem_preimage, Function.comp_apply, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      intro hx
      exact h (by simpa using ⟨π x, hT x, hx⟩)
    simp [this, hm.1]

theorem meanI_eq_sum (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    (s : X → ℝ) (T : Finset ℝ) (hT : ∀ x, s x ∈ T) :
    meanI m s = ∑ v ∈ T, v * (m (s ⁻¹' {v})).toReal :=
  meanI_factor hm h1 s T hT id

theorem mean_range_pair {s t : X → ℝ} (hs : (range s).Finite) (ht : (range t).Finite) :
    (range fun x => (s x, t x)).Finite :=
  (hs.prod ht).subset (by rintro _ ⟨x, rfl⟩; exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩)

theorem mean_range_map {s : X → ℝ} (hs : (range s).Finite) (φ : ℝ → ℝ) :
    (range fun x => φ (s x)).Finite :=
  (hs.image φ).subset (by rintro _ ⟨x, rfl⟩; exact ⟨s x, ⟨x, rfl⟩, rfl⟩)

theorem mean_range_add {s t : X → ℝ} (hs : (range s).Finite) (ht : (range t).Finite) :
    (range fun x => s x + t x).Finite :=
  ((mean_range_pair hs ht).image (fun p => p.1 + p.2)).subset
    (by rintro _ ⟨x, rfl⟩; exact ⟨(s x, t x), ⟨x, rfl⟩, rfl⟩)

theorem mean_range_const (c : ℝ) : (range fun _ : X => c).Finite :=
  (Set.finite_singleton c).subset Set.range_const_subset

theorem meanI_add (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s t : X → ℝ}
    (hs : (range s).Finite) (ht : (range t).Finite) :
    meanI m (fun x => s x + t x) = meanI m s + meanI m t := by
  classical
  let π : X → ℝ × ℝ := fun x => (s x, t x)
  have hT : ∀ x, π x ∈ hs.toFinset ×ˢ ht.toFinset := fun x => by simp [π]
  have e1 := meanI_factor hm h1 π _ hT Prod.fst
  have e2 := meanI_factor hm h1 π _ hT Prod.snd
  have e3 := meanI_factor hm h1 π _ hT (fun p => p.1 + p.2)
  simp only [Function.comp_def, π] at e1 e2 e3
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => add_mul _ _ _

theorem meanI_map (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s : X → ℝ}
    (hs : (range s).Finite) (c : ℝ) : meanI m (fun x => c * s x) = c * meanI m s := by
  classical
  have hT : ∀ x, s x ∈ hs.toFinset := fun x => by simp
  have e1 := meanI_factor hm h1 s _ hT (fun v => c * v)
  have e2 := meanI_eq_sum hm h1 s _ hT
  simp only [Function.comp_def] at e1
  rw [e1, e2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _

theorem meanI_const (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (c : ℝ) :
    meanI m (fun _ : X => c) = c := by
  have e := meanI_factor hm h1 (fun _ : X => ()) Finset.univ (fun _ => Finset.mem_univ _)
    (fun _ => c)
  simp only [Function.comp_def] at e
  rw [e]
  simp [h1]

theorem meanI_mono (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s t : X → ℝ}
    (hs : (range s).Finite) (ht : (range t).Finite) (hst : ∀ x, s x ≤ t x) :
    meanI m s ≤ meanI m t := by
  classical
  let π : X → ℝ × ℝ := fun x => (s x, t x)
  have hπ := mean_range_pair hs ht
  have hT : ∀ x, π x ∈ hπ.toFinset := fun x => (Set.Finite.mem_toFinset hπ).2 ⟨x, rfl⟩
  have e1 := meanI_factor hm h1 π _ hT Prod.fst
  have e2 := meanI_factor hm h1 π _ hT Prod.snd
  simp only [Function.comp_def, π] at e1 e2
  rw [e1, e2]
  refine Finset.sum_le_sum fun a ha => ?_
  obtain ⟨x, rfl⟩ := (Set.Finite.mem_toFinset hπ).1 ha
  exact mul_le_mul_of_nonneg_right (hst x) ENNReal.toReal_nonneg

theorem meanI_smul_inv' {H Y : Type*} [Group H] [MulAction H Y] {m : Set Y → ℝ≥0∞}
    (hinv : IsInvariant H m) (s : Y → ℝ) (g : H) :
    meanI m (fun x => s (g⁻¹ • x)) = meanI m s := by
  unfold meanI
  congr 1
  funext v
  have : (fun x => s (g⁻¹ • x)) ⁻¹' {v} = g • (s ⁻¹' {v}) := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    rfl
  rw [this, hinv]

/-! ### The upper integral on `ℓ∞` -/
local notation "E" X => lp (fun _ : X => ℝ) ∞

variable (m) in
/-- Upper Darboux integral of a bounded function. -/
noncomputable def meanP (f : E X) : ℝ :=
  sInf {r | ∃ s : X → ℝ, (range s).Finite ∧ (∀ x, (f : X → ℝ) x ≤ s x) ∧ meanI m s = r}

theorem mean_abs_le (f : E X) (x : X) : |(f : X → ℝ) x| ≤ ‖f‖ := by
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero f x
  simpa [Real.norm_eq_abs] using this

theorem meanP_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {f : E X} {s : X → ℝ}
    (hs : (range s).Finite) (hfs : ∀ x, (f : X → ℝ) x ≤ s x) : meanP m f ≤ meanI m s := by
  refine csInf_le ⟨-‖f‖, ?_⟩ ⟨s, hs, hfs, rfl⟩
  rintro _ ⟨t, ht, hft, rfl⟩
  rw [← meanI_const hm h1 (-‖f‖)]
  exact meanI_mono hm h1 (mean_range_const _) ht
    (fun x => le_trans (neg_le_of_abs_le (mean_abs_le f x)) (hft x))

theorem le_meanP {f : E X} {r : ℝ}
    (h : ∀ s : X → ℝ, (range s).Finite → (∀ x, (f : X → ℝ) x ≤ s x) → r ≤ meanI m s) :
    r ≤ meanP m f := by
  refine le_csInf ⟨_, fun _ => ‖f‖, mean_range_const _,
    fun x => le_trans (le_abs_self _) (mean_abs_le f x), rfl⟩ ?_
  rintro _ ⟨s, hs, hfs, rfl⟩
  exact h s hs hfs

/-- Approximation from above by a finitely valued function, within `ε`. -/
theorem mean_approx (f : E X) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : X → ℝ, (range s).Finite ∧ (∀ x, (f : X → ℝ) x ≤ s x) ∧
      ∀ x, s x ≤ (f : X → ℝ) x + ε := by
  refine ⟨fun x => ε * ⌈(f : X → ℝ) x / ε⌉, ?_, fun x => ?_, fun x => ?_⟩
  · refine ((Set.finite_Icc ⌈-‖f‖ / ε⌉ ⌈‖f‖ / ε⌉).image (fun k : ℤ => ε * k)).subset ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨_, ⟨Int.ceil_mono ?_, Int.ceil_mono ?_⟩, rfl⟩
    · exact div_le_div_of_nonneg_right (neg_le_of_abs_le (mean_abs_le f x)) hε.le
    · exact div_le_div_of_nonneg_right (le_trans (le_abs_self _) (mean_abs_le f x)) hε.le
  · have := Int.le_ceil ((f : X → ℝ) x / ε)
    calc (f : X → ℝ) x = ε * ((f : X → ℝ) x / ε) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hε.le
  · have := Int.ceil_lt_add_one ((f : X → ℝ) x / ε)
    calc ε * (⌈(f : X → ℝ) x / ε⌉ : ℝ) ≤ ε * ((f : X → ℝ) x / ε + 1) :=
          mul_le_mul_of_nonneg_left this.le hε.le
      _ = (f : X → ℝ) x + ε := by field_simp

/-- A finitely valued function as an element of `ℓ∞`. -/
noncomputable def meanOfFin (s : X → ℝ) (hs : (range s).Finite) : E X :=
  ⟨s, memℓp_infty_iff.2 (by
    have : (range fun i => ‖s i‖) = (fun v => ‖v‖) '' range s := by
      rw [← Set.range_comp]; rfl
    rw [this]
    exact (hs.image _).bddAbove)⟩

@[simp] theorem meanOfFin_apply (s : X → ℝ) (hs : (range s).Finite) (x : X) :
    (meanOfFin s hs : X → ℝ) x = s x := rfl

theorem meanP_ofFin (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : X → ℝ)
    (hs : (range s).Finite) : meanP m (meanOfFin s hs) = meanI m s :=
  le_antisymm (meanP_le hm h1 hs fun _ => le_rfl)
    (le_meanP fun t ht hst => meanI_mono (t := t) hm h1 hs ht hst)

theorem meanP_smul_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {c : ℝ} (hc : 0 < c)
    (f : E X) : meanP m (c • f) ≤ c * meanP m f := by
  have : meanP m (c • f) / c ≤ meanP m f := by
    refine le_meanP fun s hs hfs => ?_
    rw [div_le_iff₀ hc]
    calc meanP m (c • f) ≤ meanI m (fun x => c * s x) :=
          meanP_le hm h1 (mean_range_map hs _) (fun x => by
            simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
            exact mul_le_mul_of_nonneg_left (hfs x) hc.le)
      _ = meanI m s * c := by rw [meanI_map hm h1 hs, mul_comm]
  rwa [div_le_iff₀ hc, mul_comm] at this

theorem meanP_smul (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {c : ℝ} (hc : 0 < c)
    (f : E X) : meanP m (c • f) = c * meanP m f := by
  refine le_antisymm (meanP_smul_le hm h1 hc f) ?_
  have := meanP_smul_le hm h1 (inv_pos.2 hc) (c • f)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  calc c * meanP m f ≤ c * (c⁻¹ * meanP m (c • f)) := mul_le_mul_of_nonneg_left this hc.le
    _ = _ := by field_simp

theorem meanP_add_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f g : E X) :
    meanP m (f + g) ≤ meanP m f + meanP m g := by
  have h2 : meanP m (f + g) - meanP m f ≤ meanP m g := by
    refine le_meanP fun t ht hgt => ?_
    have : meanP m (f + g) - meanI m t ≤ meanP m f := by
      refine le_meanP fun s hs hfs => ?_
      have := meanP_le hm h1 (f := f + g) (mean_range_add hs ht)
        (fun x => by simp only [lp.coeFn_add, Pi.add_apply]; exact add_le_add (hfs x) (hgt x))
      rw [meanI_add hm h1 hs ht] at this
      linarith
    linarith
  linarith

theorem meanP_zero (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) :
    meanP m (0 : E X) = 0 := by
  refine le_antisymm ?_ ?_
  · calc meanP m (0 : E X) ≤ meanI m (fun _ => 0) :=
          meanP_le hm h1 (mean_range_const _) (fun x => by simp)
      _ = 0 := meanI_const hm h1 0
  · refine le_meanP fun s hs hfs => ?_
    rw [← meanI_const hm h1 (0 : ℝ) (X := X)]
    exact meanI_mono hm h1 (mean_range_const _) hs (fun x => by simpa using hfs x)

/-- The upper integral is linear (Hahn–Banach plus uniform approximation). -/
theorem mean_exists_linear (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) :
    ∃ L : (E X) →ₗ[ℝ] ℝ, ∀ f, L f = meanP m f := by
  obtain ⟨L, -, hL⟩ := exists_extension_of_le_sublinear
    ({ domain := ⊥, toFun := 0 } : (E X) →ₗ.[ℝ] ℝ) (meanP m)
    (fun c hc f => meanP_smul hm h1 hc f) (meanP_add_le hm h1)
    (fun x => by
      have hx : (x : E X) = 0 := (Submodule.mem_bot ℝ).1 x.2
      simp [hx, meanP_zero hm h1])
  refine ⟨L, fun f => le_antisymm (hL f) ?_⟩
  -- `L` agrees with `meanI` on finitely valued functions.
  have hLs : ∀ s hs, L (meanOfFin s hs) = meanI m s := by
    intro s hs
    refine le_antisymm ((hL _).trans (meanP_ofFin hm h1 s hs).le) ?_
    have hns := mean_range_map hs (fun v => -1 * v)
    have e : -(meanOfFin s hs) = meanOfFin (fun x => -1 * s x) hns := by
      ext x; simp
    have := hL (-(meanOfFin s hs))
    rw [map_neg, e, meanP_ofFin hm h1 _ hns, meanI_map hm h1 hs] at this
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨s, hs, hfs, hsf⟩ := mean_approx f hε
  have hs' := mean_range_map hs (fun v => v + -ε)
  have h3 : meanI m (fun x => s x + -ε) = meanI m s - ε := by
    rw [meanI_add hm h1 hs (mean_range_const _), meanI_const hm h1]; ring
  have h4 : L (meanOfFin _ hs') ≤ L f := by
    have := hL (meanOfFin _ hs' - f)
    have h0 : meanP m (meanOfFin _ hs' - f) ≤ 0 := by
      calc meanP m (meanOfFin _ hs' - f) ≤ meanI m (fun _ => 0) :=
            meanP_le hm h1 (mean_range_const _) (fun x => by
              simp only [lp.coeFn_sub, Pi.sub_apply, meanOfFin_apply]; linarith [hsf x])
        _ = 0 := meanI_const hm h1 0
    rw [map_sub] at this
    linarith
  rw [hLs] at h4
  calc meanP m f ≤ meanI m s := meanP_le hm h1 hs hfs
    _ ≤ L f + ε := by linarith

/-- **The integral** `∫ · dm` of a bounded function against a finitely additive probability
measure. -/
noncomputable def mean_integral (m : Set X → ℝ≥0∞) (hm : IsFinitelyAdditiveMeasure m)
    (h1 : m univ = 1) : (E X) →ₗ[ℝ] ℝ where
  toFun := meanP m
  map_add' f g := by
    obtain ⟨L, hL⟩ := mean_exists_linear hm h1
    rw [← hL, ← hL, ← hL, map_add]
  map_smul' c f := by
    obtain ⟨L, hL⟩ := mean_exists_linear hm h1
    rw [← hL, ← hL, map_smul]; rfl

theorem mean_integral_apply (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X) :
    mean_integral m hm h1 f = meanP m f := rfl

theorem mean_integral_nonneg (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (hf : ∀ x, 0 ≤ (f : X → ℝ) x) : 0 ≤ mean_integral m hm h1 f := by
  refine le_meanP fun s hs hfs => ?_
  rw [← meanI_const hm h1 (0 : ℝ) (X := X)]
  exact meanI_mono hm h1 (mean_range_const _) hs (fun x => (hf x).trans (hfs x))

theorem mean_integral_eq_const (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (c : ℝ) (hf : ∀ x, (f : X → ℝ) x = c) : mean_integral m hm h1 f = c := by
  have : f = meanOfFin (fun _ => c) (mean_range_const c) := by ext x; simp [hf]
  rw [this, mean_integral_apply, meanP_ofFin hm h1, meanI_const hm h1]

theorem mean_range_indicator (A : Set X) : (range (A.indicator (1 : X → ℝ))).Finite :=
  (Set.toFinite ({0, 1} : Set ℝ)).subset (by
    rintro _ ⟨x, rfl⟩; by_cases h : x ∈ A <;> simp [h])

/-- The indicator function of `A` as an element of `ℓ∞`. -/
noncomputable def mean_ind (A : Set X) : E X := meanOfFin _ (mean_range_indicator A)

@[simp] theorem mean_ind_apply (A : Set X) (x : X) :
    (mean_ind A : X → ℝ) x = A.indicator 1 x := rfl

theorem mean_integral_abs_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X) :
    |mean_integral m hm h1 f| ≤ ‖f‖ := by
  rw [mean_integral_apply, abs_le]
  constructor
  · refine le_meanP fun s hs hfs => ?_
    rw [← meanI_const hm h1 (-‖f‖) (X := X)]
    exact meanI_mono hm h1 (mean_range_const _) hs
      (fun x => (neg_le_of_abs_le (mean_abs_le f x)).trans (hfs x))
  · exact (meanP_le hm h1 (mean_range_const ‖f‖) (fun x => (le_abs_self _).trans
      (mean_abs_le f x))).trans (meanI_const hm h1 _).le

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {Q : Type*} (m : Set Q → ℝ≥0∞)
/-! ### The mean as a function on bounded functions -/
/-- A bounded function as an element of `ℓ∞`. -/
noncomputable def toLinf (a : Q → ℝ) (B : ℝ) (ha : ∀ q, |a q| ≤ B) :
    lp (fun _ : Q => ℝ) ∞ :=
  ⟨a, memℓp_infty_iff.2 ⟨B, by rintro _ ⟨q, rfl⟩; simpa [Real.norm_eq_abs] using ha q⟩⟩

/-- The mean of a function on `Q` (junk `0` if unbounded). -/
noncomputable def Mn (a : Q → ℝ) : ℝ :=
  open Classical in
  if h : BddAbove (Set.range fun q => ‖a q‖) then meanP m ⟨a, memℓp_infty_iff.2 h⟩ else 0

lemma Mn_eq {a : Q → ℝ} {B : ℝ} (ha : ∀ q, |a q| ≤ B) : Mn m a = meanP m (toLinf a B ha) := by
  have h : BddAbove (Set.range fun q => ‖a q‖) :=
    ⟨B, by rintro _ ⟨q, rfl⟩; simpa [Real.norm_eq_abs] using ha q⟩
  simp only [Mn, dif_pos h]
  rfl

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {Q : Type*} (m : Set Q → ℝ≥0∞)
variable {m} (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
include hm h1
lemma Mn_add {a b : Q → ℝ} {A B : ℝ} (ha : ∀ q, |a q| ≤ A) (hb : ∀ q, |b q| ≤ B) :
    Mn m (fun q => a q + b q) = Mn m a + Mn m b := by
  have hab : ∀ q, |a q + b q| ≤ A + B := fun q =>
    (abs_add_le _ _).trans (add_le_add (ha q) (hb q))
  rw [Mn_eq m hab, Mn_eq m ha, Mn_eq m hb, ← mean_integral_apply hm h1,
    ← mean_integral_apply hm h1, ← mean_integral_apply hm h1, ← map_add]
  rfl

lemma Mn_smul (c : ℝ) {a : Q → ℝ} {A : ℝ} (ha : ∀ q, |a q| ≤ A) :
    Mn m (fun q => c * a q) = c * Mn m a := by
  have hca : ∀ q, |c * a q| ≤ |c| * A := fun q => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ha q) (abs_nonneg c)
  have e : toLinf (fun q => c * a q) _ hca = c • toLinf a A ha := by ext; rfl
  rw [Mn_eq m hca, Mn_eq m ha, ← mean_integral_apply hm h1, ← mean_integral_apply hm h1, e,
    map_smul, smul_eq_mul]

lemma Mn_nonneg {a : Q → ℝ} {A : ℝ} (ha : ∀ q, |a q| ≤ A) (h0 : ∀ q, 0 ≤ a q) :
    0 ≤ Mn m a := by
  rw [Mn_eq m ha, ← mean_integral_apply hm h1]
  exact mean_integral_nonneg hm h1 _ h0

lemma Mn_const (c : ℝ) : Mn m (fun _ : Q => c) = c := by
  rw [Mn_eq m (B := |c|) (fun _ => le_rfl), ← mean_integral_apply hm h1]
  exact mean_integral_eq_const hm h1 _ c (fun _ => rfl)

lemma Mn_abs_le {a : Q → ℝ} {A : ℝ} (ha : ∀ q, |a q| ≤ A) : |Mn m a| ≤ A := by
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · exfalso
    have : (Set.univ : Set Q) = ∅ := Set.univ_eq_empty_iff.2 hQ
    rw [this, hm.1] at h1
    exact zero_ne_one h1
  obtain ⟨q⟩ := hQ
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha q)
  rw [Mn_eq m ha, ← mean_integral_apply hm h1]
  refine (mean_integral_abs_le hm h1 _).trans (lp.norm_le_of_forall_le hA fun q => ?_)
  rw [Real.norm_eq_abs]
  exact ha q

lemma Mn_sub_le {a b : Q → ℝ} {B ε : ℝ} (hb : ∀ q, |b q| ≤ B)
    (hab : ∀ q, |a q - b q| ≤ ε) : |Mn m a - Mn m b| ≤ ε := by
  have e : Mn m a = Mn m (fun q => (a q - b q) + b q) + 0 := by simp
  rw [e, Mn_add hm h1 hab hb]
  simpa using Mn_abs_le hm h1 hab

lemma meanP_comp_le {H : Type*} [Group H] [MulAction H Q] (hinv : IsInvariant H m) (g : H)
    {a : Q → ℝ} {B : ℝ} (ha : ∀ q, |a q| ≤ B) (ha' : ∀ q, |a (g⁻¹ • q)| ≤ B) :
    meanP m (toLinf (fun q => a (g⁻¹ • q)) B ha') ≤ meanP m (toLinf a B ha) := by
  refine le_meanP fun s hs hfs => ?_
  rw [← meanI_smul_inv' hinv s g]
  exact meanP_le hm h1 ((hs.image id).subset (by rintro _ ⟨x, rfl⟩; exact ⟨_, ⟨_, rfl⟩, rfl⟩))
    (fun x => hfs _)

lemma Mn_inv {H : Type*} [Group H] [MulAction H Q] (hinv : IsInvariant H m) (g : H)
    {a : Q → ℝ} {B : ℝ} (ha : ∀ q, |a q| ≤ B) :
    Mn m (fun q => a (g⁻¹ • q)) = Mn m a := by
  have ha' : ∀ q, |a (g⁻¹ • q)| ≤ B := fun q => ha _
  rw [Mn_eq m ha', Mn_eq m ha]
  refine le_antisymm (meanP_comp_le hm h1 hinv g ha ha') ?_
  have := meanP_comp_le hm h1 hinv g⁻¹ ha' (fun q => ha' _)
  have e : toLinf (fun q => a (g⁻¹ • g⁻¹⁻¹ • q)) B (fun q => ha' _) = toLinf a B ha := by
    ext q
    show a (g⁻¹ • g⁻¹⁻¹ • q) = a q
    simp
  rw [e] at this
  exact this

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
lemma isBddMeasOn_add' {R : Set (X × X)} {f g : X × X → ℝ} (hf : IsBddMeasOn R f)
    (hg : IsBddMeasOn R g) : IsBddMeasOn R (f + g) := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := hg.2
  exact ⟨hf.1.add hg.1, C + D, fun p hp => (abs_add_le _ _).trans (add_le_add (hC p hp) (hD p hp))⟩

lemma isBddMeasOn_smul' {R : Set (X × X)} (c : ℝ) {f : X × X → ℝ} (hf : IsBddMeasOn R f) :
    IsBddMeasOn R (c • f) := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨hf.1.const_smul c, |c| * C, fun p hp => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg c)

lemma isBddMeasOn_const' {R : Set (X × X)} (c : ℝ) : IsBddMeasOn R (fun _ => c) :=
  ⟨measurable_const, |c|, fun _ _ => le_rfl⟩

lemma isBddMeasOn_one' {R : Set (X × X)} : IsBddMeasOn R (1 : X × X → ℝ) :=
  ⟨measurable_const, 1, fun _ _ => by simp⟩

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
variable {R : Set (X × X)} {P : (X × X → ℝ) → X → ℝ} (hP : IsLeftInvariantMean μ R P)
include hP
lemma lim_le_of_le {f g : X × X → ℝ} (hf : IsBddMeasOn R f) (hg : IsBddMeasOn R g)
    (hfg : ∀ p ∈ R, f p ≤ g p) : ∀ᵐ x ∂μ, P f x ≤ P g x := by
  have hb := isBddMeasOn_smul' (-1 : ℝ) hf
  have h := hP.nonneg (g + (-1 : ℝ) • f) (isBddMeasOn_add' hg hb) (fun p hp => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hfg p hp])
  filter_upwards [h, hP.add g ((-1 : ℝ) • f) hg hb, hP.smul (-1) f hf] with x h1 h2 h3
  rw [h2, Pi.add_apply, h3] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  linarith

lemma lim_const (c : ℝ) : P (fun _ => c) =ᵐ[μ] fun _ => c := by
  have e : (fun _ : X × X => c) = c • (1 : X × X → ℝ) := by funext; simp
  rw [e]
  filter_upwards [hP.smul c 1 isBddMeasOn_one', hP.one] with x h1 h2
  rw [h1, Pi.smul_apply, h2]
  simp

lemma lim_abs_le {f : X × X → ℝ} (hf : IsBddMeasOn R f) {C : ℝ} (hC : ∀ p ∈ R, |f p| ≤ C) :
    ∀ᵐ x ∂μ, |P f x| ≤ C := by
  have h1 := lim_le_of_le hP hf (isBddMeasOn_const' C) (fun p hp => (le_abs_self _).trans (hC p hp))
  have h2 := lim_le_of_le hP (isBddMeasOn_const' (-C)) hf (fun p hp => neg_le_of_abs_le (hC p hp))
  filter_upwards [h1, h2, lim_const hP C, lim_const hP (-C)] with x a b c e
  rw [c] at a
  rw [e] at b
  exact abs_le.2 ⟨b, a⟩

open Classical in
lemma lim_loc (hrefl : ∀ x, (x, x) ∈ R) {B : Set X} (hB : MeasurableSet B) {f : X × X → ℝ}
    (hf : IsBddMeasOn R f) :
    P (fun p => if p.1 ∈ B then f p else 0) =ᵐ[μ] fun y => if y ∈ B then P f y else 0 := by
  let φ : PartialTransformation R :=
    { dom := B, cod := B, measurableSet_dom := hB, measurableSet_cod := hB,
      e := MeasurableEquiv.refl B, graph_subset := fun a => hrefl a }
  have h1 : φ.shiftRel f = fun p => if p.1 ∈ B then f p else 0 := by
    funext p
    by_cases h : p.1 ∈ B <;> simp [PartialTransformation.shiftRel, h, φ]
  have h2 : φ.shiftBase (P f) = fun y => if y ∈ B then P f y else 0 := by
    funext y
    by_cases h : y ∈ B <;> simp [PartialTransformation.shiftBase, h, φ]
  rw [← h1, ← h2]
  exact hP.invariant φ f hf

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
/-- Transfer of a left invariant mean between measures with the same null sets. -/
lemma lim_of_ae_eq {X : Type*} [MeasurableSpace X] {μ ν : Measure X} (h : ae μ = ae ν)
    {R : Set (X × X)} {P : (X × X → ℝ) → X → ℝ} (hP : Monod.IsLeftInvariantMean μ R P) :
    Monod.IsLeftInvariantMean ν R P := by
  have h0 : ∀ s, μ s = 0 ↔ ν s = 0 := fun s => by
    rw [measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem, h]
  refine
    { aemeasurable := fun f hf => ?_
      congr := fun f g hf hg hfg => ?_
      add := fun f g hf hg => ?_
      smul := fun c f hf => ?_
      nonneg := fun f hf hpos => ?_
      one := ?_
      invariant := fun φ f hf => ?_ }
  · obtain ⟨g, hg, he⟩ := hP.aemeasurable f hf
    exact ⟨g, hg, by rw [← h]; exact he⟩
  · have := hP.congr f g hf hg ((h0 _).2 hfg)
    rwa [h] at this
  · have := hP.add f g hf hg
    rwa [h] at this
  · have := hP.smul c f hf
    rwa [h] at this
  · have := hP.nonneg f hf hpos
    rwa [h] at this
  · have := hP.one
    rwa [h] at this
  · have := hP.invariant φ f hf
    rwa [h] at this

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
open Classical in
/-- `φ⁻¹` on the image of `φ`, extended by the identity. -/
noncomputable def psi (y : X) : X := if h : y ∈ φ.cod then (φ.e.symm ⟨y, h⟩ : X) else y

lemma psi_of_mem {y : X} (h : y ∈ φ.cod) : psi φ y = φ.e.symm ⟨y, h⟩ := by
  simp only [psi, dif_pos h]

lemma measurable_psi : Measurable (psi φ) := by
  classical
  unfold psi
  exact Measurable.dite (measurable_subtype_coe.comp φ.e.symm.measurable) measurable_subtype_coe
    φ.measurableSet_cod

lemma psi_mem_R {y : X} (h : y ∈ φ.cod) : (psi φ y, y) ∈ R := by
  have := φ.graph_subset (φ.e.symm ⟨y, h⟩)
  rw [psi_of_mem φ h]
  simpa using this

open Classical in
lemma shiftRel_eq' (f : X × X → ℝ) :
    φ.shiftRel f = fun p => if p.1 ∈ φ.cod then f (psi φ p.1, p.2) else 0 := by
  funext p
  by_cases h : p.1 ∈ φ.cod
  · simp [PartialTransformation.shiftRel, h, psi_of_mem φ h]
  · simp [PartialTransformation.shiftRel, h]

open Classical in
lemma shiftBase_eq' (F : X → ℝ) :
    φ.shiftBase F = fun y => if y ∈ φ.cod then F (psi φ y) else 0 := by
  funext y
  by_cases h : y ∈ φ.cod
  · simp [PartialTransformation.shiftBase, h, psi_of_mem φ h]
  · simp [PartialTransformation.shiftBase, h]

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
lemma ae_eq_of_setInt {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ A, MeasurableSet A → ∫ x in A, f x ∂μ = ∫ x in A, g x ∂μ) : f =ᵐ[μ] g :=
  Integrable.ae_eq_of_forall_setIntegral_eq f g hf hg (fun A hA _ => h A hA)

lemma abs_setInt_le [IsFiniteMeasure μ] {u : X → ℝ} {C : ℝ} (hb : ∀ᵐ x ∂μ, |u x| ≤ C)
    (A : Set X) : |∫ x in A, u x ∂μ| ≤ C * μ.real A := by
  rw [← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top μ A)
    (ae_restrict_of_ae (by filter_upwards [hb] with x hx; rwa [Real.norm_eq_abs]))

lemma abs_integral_mul_le {u D : X → ℝ} {C : ℝ}
    (hb : ∀ᵐ x ∂μ, |u x| ≤ C) (hD : Integrable D μ) :
    |∫ x, u x * D x ∂μ| ≤ C * ∫ x, |D x| ∂μ := by
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hD.abs.const_mul C) ?_
  filter_upwards [hb] with x hx
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

lemma integrable_mul_of_bdd {u D : X → ℝ} {C : ℝ} (hu : AEStronglyMeasurable u μ)
    (hb : ∀ᵐ x ∂μ, |u x| ≤ C) (hD : Integrable D μ) : Integrable (fun x => u x * D x) μ :=
  hD.bdd_mul hu (by filter_upwards [hb] with x hx; rwa [Real.norm_eq_abs])

lemma abs_integral_mul_sub_le' {u D D' : X → ℝ} {C : ℝ} (hu : AEStronglyMeasurable u μ)
    (hb : ∀ᵐ x ∂μ, |u x| ≤ C) (hD : Integrable D μ) (hD' : Integrable D' μ) :
    |∫ x, u x * D x ∂μ - ∫ x, u x * D' x ∂μ| ≤ C * ∫ x, |D x - D' x| ∂μ := by
  rw [← integral_sub (integrable_mul_of_bdd μ hu hb hD) (integrable_mul_of_bdd μ hu hb hD')]
  have : (fun x => u x * D x - u x * D' x) = fun x => u x * (D x - D' x) := by
    funext x; ring
  rw [this]
  exact abs_integral_mul_le μ hb (hD.sub hD')

lemma indicator_one_mul' (A : Set X) (h : X → ℝ) :
    (fun x => h x * A.indicator 1 x) = A.indicator h := by
  funext x
  by_cases hx : x ∈ A <;> simp [hx]

lemma abs_sub_clamp_le' (d M : ℝ) (hM : 0 ≤ M) : |d - max (min d M) (-M)| ≤ |d| := by
  rcases le_total d M with h1 | h1
  · rw [min_eq_left h1]
    rcases le_total d (-M) with h2 | h2
    · rw [max_eq_right h2, abs_of_nonpos (by linarith : d - -M ≤ 0),
        abs_of_nonpos (by linarith : d ≤ 0)]
      linarith
    · rw [max_eq_left h2]
      simp
  · rw [min_eq_right h1, max_eq_left (by linarith : -M ≤ M),
      abs_of_nonneg (by linarith : 0 ≤ d - M), abs_of_nonneg (by linarith : 0 ≤ d)]
    linarith

lemma clamp_eq' {d M : ℝ} (h : |d| ≤ M) : max (min d M) (-M) = d := by
  rw [min_eq_left (abs_le.1 h).2, max_eq_left (abs_le.1 h).1]

/-- Truncations of an integrable function converge to it in `L¹`. -/
lemma tendsto_clamp {D : X → ℝ} (hD : Measurable D) (hDi : Integrable D μ) :
    Tendsto (fun M : ℕ => ∫ x, |D x - max (min (D x) M) (-M)| ∂μ) atTop (𝓝 0) := by
  have hclm : ∀ M : ℕ, Measurable (fun x => max (min (D x) M) (-(M : ℝ))) := fun M =>
    (hD.min measurable_const).max measurable_const
  have := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun (M : ℕ) x => |D x - max (min (D x) M) (-M)|) (f := fun _ => (0 : ℝ))
    (fun x => |D x|)
    (fun M => (hD.sub (hclm M)).abs.aestronglyMeasurable) hDi.abs
    (fun M => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_sub_clamp_le' _ _ (Nat.cast_nonneg M))
    (Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|D x|⌉₊] with M hM
      have : |D x| ≤ M := (Nat.le_ceil _).trans (by exact_mod_cast hM)
      simp only [clamp_eq' this, sub_self, abs_zero])
  simpa using this

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
open Classical in
/-- The Riesz representative of a functional (junk `0` if there is none). -/
noncomputable def Rep (L : E → ℝ) : E :=
  if h : ∃ v, ∀ w, inner ℝ v w = L w then h.choose else 0

lemma inner_Rep {L : E → ℝ} (hadd : ∀ a b, L (a + b) = L a + L b)
    (hsmul : ∀ (c : ℝ) a, L (c • a) = c * L a) {B : ℝ} (hB : ∀ a, |L a| ≤ B * ‖a‖) (w : E) :
    inner ℝ (Rep L) w = L w := by
  let L' : E →ₗ[ℝ] ℝ := { toFun := L, map_add' := hadd, map_smul' := hsmul }
  let Φ : StrongDual ℝ E := L'.mkContinuous B (fun a => by rw [Real.norm_eq_abs]; exact hB a)
  have h : ∃ v, ∀ w, inner ℝ v w = L w := ⟨(InnerProductSpace.toDual ℝ E).symm Φ, fun w => by
    rw [InnerProductSpace.toDual_symm_apply]
    rfl⟩
  simp only [Rep, dif_pos h]
  exact h.choose_spec w

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
/-! ## The data of the relative Zimmer theorem -/
/-- The orbit relation of a subgroup. -/
def RG {X G : Type*} [Group G] [MulAction G X] (Γ : Subgroup G) : Set (X × X) :=
  {p | ∃ g ∈ Γ, g • p.1 = p.2}

/-- All hypotheses of the theorem, for a finite measure, with the mean `P_Γ` and the invariant
finitely additive probability `m` on `Λ ⧸ Γ` chosen. -/
structure Data {X : Type*} [MeasurableSpace X] (μ : Measure X) (G : Type*) [Group G]
    [MulAction G X] where
  Γ : Subgroup G
  Λ : Subgroup G
  hΓΛ : Γ ≤ Λ
  hmeas : ∀ g ∈ Λ, Measurable (fun x : X => g • x)
  hnull : ∀ g ∈ Λ, ∀ s : Set X, μ s = 0 → μ ((fun x : X => g • x) ⁻¹' s) = 0
  PΓ : (X × X → ℝ) → X → ℝ
  hPΓ : Monod.IsLeftInvariantMean μ (RG Γ) PΓ
  R : Set (X × X)
  X₀ : Set X
  hX₀ : MeasurableSet X₀
  hX₀c : μ X₀ᶜ = 0
  hsat : ∀ p ∈ R, (p.1 ∈ X₀ ↔ p.2 ∈ X₀)
  hΛR : ∀ g ∈ Λ, ∀ x ∈ X₀, (x, g • x) ∈ R
  C : Set G
  hC : C.Countable
  hCΛ : C ⊆ Λ
  hRC : ∀ p ∈ R, p.1 ∈ X₀ → ∃ g ∈ C, g • p.1 = p.2
  m : Set (Λ ⧸ Γ.subgroupOf Λ) → ℝ≥0∞
  hm : IsFinitelyAdditiveMeasure m
  hm1 : m univ = 1
  hminv : IsInvariant Λ m

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
  (d : Data μ G)
/-- The coset space `Λ ⧸ Γ`. -/
abbrev Q := d.Λ ⧸ d.Γ.subgroupOf d.Λ

lemma refl (x : X) : (x, x) ∈ (RG d.Γ : Set (X × X)) := ⟨1, d.Γ.one_mem, one_smul _ _⟩

lemma smul_mem_X₀ {g : G} (hg : g ∈ d.Λ) {x : X} (hx : x ∈ d.X₀) : g • x ∈ d.X₀ :=
  (d.hsat _ (d.hΛR g hg x hx)).1 hx

lemma smul_mem_X₀_iff {g : G} (hg : g ∈ d.Λ) {x : X} : g • x ∈ d.X₀ ↔ x ∈ d.X₀ :=
  ⟨fun h => by simpa using d.smul_mem_X₀ (inv_mem hg) h, d.smul_mem_X₀ hg⟩

lemma qmp {g : G} (hg : g ∈ d.Λ) : Measure.QuasiMeasurePreserving (fun x : X => g • x) μ μ :=
  ⟨d.hmeas g hg, Measure.AbsolutelyContinuous.mk fun s hs h0 => by
    rw [Measure.map_apply (d.hmeas g hg) hs]
    exact d.hnull g hg s h0⟩

/-- Measurable, and bounded by `C` on the `Λ`-orbit relation over `X₀`. -/
def BddMC (g : X × X → ℝ) (C : ℝ) : Prop :=
  Measurable g ∧ 0 ≤ C ∧ ∀ x ∈ d.X₀, ∀ k ∈ d.Λ, |g (x, k • x)| ≤ C

/-- `g_λ (w, z) = g (λ w, z)` when `λ w ∈ X₀`. -/
noncomputable def Gl (l : d.Λ) (g : X × X → ℝ) : X × X → ℝ := fun p =>
  if (l : G) • p.1 ∈ d.X₀ then g ((l : G) • p.1, p.2) else 0

/-- `F_λ = P_Γ (g_λ) ∘ λ⁻¹`. -/
noncomputable def Fl (l : d.Λ) (g : X × X → ℝ) : X → ℝ := fun y =>
  d.PΓ (d.Gl l g) ((l : G)⁻¹ • y)

lemma measurable_Gl (l : d.Λ) {g : X × X → ℝ} (hg : Measurable g) : Measurable (d.Gl l g) :=
  Measurable.ite ((d.hX₀).preimage ((d.hmeas _ l.2).comp measurable_fst))
    (hg.comp (((d.hmeas _ l.2).comp measurable_fst).prodMk measurable_snd)) measurable_const

lemma abs_Gl_le (l : d.Λ) {g : X × X → ℝ} {C : ℝ} (hg : d.BddMC g C) :
    ∀ p ∈ (RG d.Γ : Set (X × X)), |d.Gl l g p| ≤ C := by
  rintro ⟨w, z⟩ ⟨γ, hγ, hz⟩
  simp only at hz
  subst hz
  simp only [Gl]
  split_ifs with h
  · have := hg.2.2 _ h (γ * (l : G)⁻¹) (mul_mem (d.hΓΛ hγ) (inv_mem l.2))
    simpa [mul_smul] using this
  · simpa using hg.2.1

lemma bdd_Gl (l : d.Λ) {g : X × X → ℝ} {C : ℝ} (hg : d.BddMC g C) :
    IsBddMeasOn (RG d.Γ) (d.Gl l g) :=
  ⟨d.measurable_Gl l hg.1, C, d.abs_Gl_le l hg⟩

lemma PΓ_shift {γ : G} (hγ : γ ∈ d.Γ) {g : X × X → ℝ} (hg : IsBddMeasOn (RG d.Γ) g) :
    d.PΓ (fun p => g (γ • p.1, p.2)) =ᵐ[μ] fun w => d.PΓ g (γ • w) := by
  have hm := d.hmeas γ (d.hΓΛ hγ)
  have hm' := d.hmeas γ⁻¹ (inv_mem (d.hΓΛ hγ))
  let e : (univ : Set X) ≃ᵐ (univ : Set X) :=
    { toFun := fun a => ⟨γ⁻¹ • (a : X), trivial⟩
      invFun := fun b => ⟨γ • (b : X), trivial⟩
      left_inv := fun a => by ext; simp
      right_inv := fun b => by ext; simp
      measurable_toFun := (hm'.comp measurable_subtype_coe).subtype_mk
      measurable_invFun := (hm.comp measurable_subtype_coe).subtype_mk }
  let φ : PartialTransformation (RG d.Γ : Set (X × X)) :=
    { dom := univ, cod := univ, measurableSet_dom := MeasurableSet.univ,
      measurableSet_cod := MeasurableSet.univ, e := e,
      graph_subset := fun a => ⟨γ⁻¹, inv_mem hγ, rfl⟩ }
  have h1 : φ.shiftRel g = fun p => g (γ • p.1, p.2) := by
    funext p
    simp [PartialTransformation.shiftRel, φ, e]
  have h2 : φ.shiftBase (d.PΓ g) = fun w => d.PΓ g (γ • w) := by
    funext w
    simp [PartialTransformation.shiftBase, φ, e]
  rw [← h1, ← h2]
  exact d.hPΓ.invariant φ g hg

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
  (d : Data μ G)
variable {g g' : X × X → ℝ} {C C' : ℝ}
/-! ### The functions `F_λ` -/
lemma aesm_Fl (l : d.Λ) (hg : d.BddMC g C) : AEStronglyMeasurable (d.Fl l g) μ :=
  ((d.hPΓ.aemeasurable _ (d.bdd_Gl l hg)).comp_quasiMeasurePreserving
    (d.qmp (inv_mem l.2))).aestronglyMeasurable

lemma ae_abs_Fl_le (l : d.Λ) (hg : d.BddMC g C) : ∀ᵐ y ∂μ, |d.Fl l g y| ≤ C :=
  (d.qmp (inv_mem l.2)).ae (lim_abs_le d.hPΓ (d.bdd_Gl l hg) (d.abs_Gl_le l hg))

lemma Fl_add (l : d.Λ) (hg : d.BddMC g C) (hg' : d.BddMC g' C') :
    d.Fl l (g + g') =ᵐ[μ] d.Fl l g + d.Fl l g' := by
  have e : d.Gl l (g + g') = d.Gl l g + d.Gl l g' := by
    funext p
    simp only [Gl, Pi.add_apply]
    split_ifs <;> simp
  have := d.hPΓ.add _ _ (d.bdd_Gl l hg) (d.bdd_Gl l hg')
  rw [← e] at this
  exact (d.qmp (inv_mem l.2)).ae_eq this

lemma Fl_smul (l : d.Λ) (c : ℝ) (hg : d.BddMC g C) :
    d.Fl l (c • g) =ᵐ[μ] c • d.Fl l g := by
  have e : d.Gl l (c • g) = c • d.Gl l g := by
    funext p
    simp only [Gl, Pi.smul_apply]
    split_ifs <;> simp
  have := d.hPΓ.smul c _ (d.bdd_Gl l hg)
  rw [← e] at this
  exact (d.qmp (inv_mem l.2)).ae_eq this

lemma Fl_congr (l : d.Λ) (hg : d.BddMC g C) (hg' : d.BddMC g' C') {N : Set X} (hN : μ N = 0)
    (h : ∀ x ∈ d.X₀, x ∉ N → ∀ k ∈ d.Λ, g (x, k • x) = g' (x, k • x)) :
    d.Fl l g =ᵐ[μ] d.Fl l g' := by
  have hrn : RelNull μ (RG d.Γ) {p | d.Gl l g p ≠ d.Gl l g' p} := by
    refine measure_mono_null ?_ (d.hnull _ l.2 N hN)
    rintro _ ⟨⟨w, z⟩, ⟨hne, γ, hγ, hz⟩, rfl⟩
    simp only at hz
    subst hz
    simp only [mem_preimage]
    by_contra hwN
    apply hne
    simp only [Gl]
    split_ifs with hw
    · have := h _ hw hwN (γ * (l : G)⁻¹) (mul_mem (d.hΓΛ hγ) (inv_mem l.2))
      simpa [mul_smul] using this
    · rfl
  exact (d.qmp (inv_mem l.2)).ae_eq (d.hPΓ.congr _ _ (d.bdd_Gl l hg) (d.bdd_Gl l hg') hrn)

lemma bddMC_one : d.BddMC (1 : X × X → ℝ) 1 :=
  ⟨measurable_const, zero_le_one, fun _ _ _ _ => by simp⟩

lemma Fl_one (l : d.Λ) : d.Fl l (1 : X × X → ℝ) =ᵐ[μ] 1 := by
  have hrn : RelNull μ (RG d.Γ) {p | d.Gl l (1 : X × X → ℝ) p ≠ (1 : X × X → ℝ) p} := by
    refine measure_mono_null ?_ (d.hnull _ l.2 _ d.hX₀c)
    rintro _ ⟨⟨w, z⟩, ⟨hne, -⟩, rfl⟩
    simp only [mem_preimage, mem_compl_iff]
    intro hw
    apply hne
    simp [Gl, hw]
  have h1 := d.hPΓ.congr _ _ (d.bdd_Gl l d.bddMC_one) isBddMeasOn_one' hrn
  exact (d.qmp (inv_mem l.2)).ae_eq (h1.trans d.hPΓ.one)

lemma Fl_nonneg (l : d.Λ) (hg : d.BddMC g C)
    (h0 : ∀ x ∈ d.X₀, ∀ k ∈ d.Λ, 0 ≤ g (x, k • x)) : ∀ᵐ y ∂μ, 0 ≤ d.Fl l g y := by
  refine (d.qmp (inv_mem l.2)).ae (d.hPΓ.nonneg _ (d.bdd_Gl l hg) ?_)
  rintro ⟨w, z⟩ ⟨γ, hγ, hz⟩
  simp only at hz
  subst hz
  simp only [Gl]
  split_ifs with h
  · have := h0 _ h (γ * (l : G)⁻¹) (mul_mem (d.hΓΛ hγ) (inv_mem l.2))
    simpa [mul_smul] using this
  · exact le_rfl

lemma Fl_loc (l : d.Λ) (hg : d.BddMC g C) {B : Set X} (hB : MeasurableSet B) :
    d.Fl l (fun p => if p.1 ∈ B then g p else 0) =ᵐ[μ] B.indicator (d.Fl l g) := by
  set B' := (fun w : X => (l : G) • w) ⁻¹' B
  have hB' : MeasurableSet B' := hB.preimage (d.hmeas _ l.2)
  have e : d.Gl l (fun p => if p.1 ∈ B then g p else 0) =
      fun p => if p.1 ∈ B' then d.Gl l g p else 0 := by
    funext p
    simp only [Gl, B', mem_preimage]
    split_ifs <;> rfl
  have := lim_loc d.hPΓ d.refl hB' (d.bdd_Gl l hg)
  rw [← e] at this
  filter_upwards [(d.qmp (inv_mem l.2)).ae_eq this] with y hy
  simp only [Function.comp_apply] at hy
  rw [Set.indicator_apply]
  simp only [Fl, hy, B', mem_preimage, smul_inv_smul]

lemma Fl_rep {l l' : d.Λ} (h : (l : d.Q) = (l' : d.Q)) (hg : d.BddMC g C) :
    d.Fl l g =ᵐ[μ] d.Fl l' g := by
  have hmem := QuotientGroup.eq.1 h
  set γ : G := ((l⁻¹ * l' : d.Λ) : G)
  have hγ : γ ∈ d.Γ := Subgroup.mem_subgroupOf.1 hmem
  have hl' : (l' : G) = (l : G) * γ := by simp [γ]
  have e : d.Gl l' g = fun p => d.Gl l g (γ • p.1, p.2) := by
    funext p
    simp [Gl, hl', mul_smul]
  have := d.PΓ_shift hγ (d.bdd_Gl l hg)
  rw [← e] at this
  filter_upwards [(d.qmp (inv_mem l'.2)).ae_eq this] with y hy
  simp only [Function.comp_apply] at hy
  show d.PΓ (d.Gl l g) ((l : G)⁻¹ • y) = d.PΓ (d.Gl l' g) ((l' : G)⁻¹ • y)
  rw [hy, hl', mul_inv_rev, mul_smul, smul_inv_smul]

/-- The translate `g ∘ (κ⁻¹ × id)` over `X₀`. -/
noncomputable def tr (κ : d.Λ) (g : X × X → ℝ) : X × X → ℝ := fun p =>
  if p.1 ∈ d.X₀ then g ((κ : G)⁻¹ • p.1, p.2) else 0

lemma Gl_tr (κ l : d.Λ) (g : X × X → ℝ) : d.Gl l (d.tr κ g) = d.Gl (κ⁻¹ * l) g := by
  funext p
  simp only [Gl, tr, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
  rw [d.smul_mem_X₀_iff (inv_mem κ.2)]
  split_ifs <;> rfl

lemma Fl_tr (κ l : d.Λ) (g : X × X → ℝ) (y : X) :
    d.Fl l (d.tr κ g) y = d.Fl (κ⁻¹ * l) g ((κ : G)⁻¹ • y) := by
  simp only [Fl, Gl_tr, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_smul,
    smul_inv_smul]

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
  (d : Data μ G)
variable [IsFiniteMeasure μ] {g g' : X × X → ℝ} {C C' : ℝ}
/-! ### The mean `P` -/
/-- `F_λ` in `L²`. -/
noncomputable def FL (l : d.Λ) (g : X × X → ℝ) : Lp ℝ 2 μ :=
  if h : MemLp (d.Fl l g) 2 μ then h.toLp _ else 0

/-- `P g ∈ L²`: the Riesz representative of `h ↦ Mn (q ↦ ⟪F_{rep q}, h⟫)`. -/
noncomputable def PL (g : X × X → ℝ) : Lp ℝ 2 μ :=
  Rep (fun w => Mn d.m (fun q : d.Q => inner ℝ (d.FL q.out g) w))

/-- The mean `P` on `R`. -/
noncomputable def P (g : X × X → ℝ) : X → ℝ := (d.PL g : X → ℝ)

/-- The constant `μ(X)^{1/2}`. -/
noncomputable def Kμ (μ : Measure X) : ℝ :=
  ((measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : NNReal) : ℝ)

lemma memLp_Fl (l : d.Λ) (hg : d.BddMC g C) : MemLp (d.Fl l g) 2 μ :=
  MemLp.of_bound (d.aesm_Fl l hg) C (by
    filter_upwards [d.ae_abs_Fl_le l hg] with y hy
    rwa [Real.norm_eq_abs])

lemma FL_eq (l : d.Λ) (hg : d.BddMC g C) : d.FL l g = (d.memLp_Fl l hg).toLp _ := by
  simp only [FL, dif_pos (d.memLp_Fl l hg)]

lemma coe_FL (l : d.Λ) (hg : d.BddMC g C) : (d.FL l g : X → ℝ) =ᵐ[μ] d.Fl l g := by
  rw [d.FL_eq l hg]
  exact MemLp.coeFn_toLp _

lemma norm_FL_le (l : d.Λ) (hg : d.BddMC g C) : ‖d.FL l g‖ ≤ Kμ μ * C := by
  refine Lp.norm_le_of_ae_bound hg.2.1 ?_
  filter_upwards [d.coe_FL l hg, d.ae_abs_Fl_le l hg] with y h1 h2
  rw [h1, Real.norm_eq_abs]
  exact h2

lemma inner_PL (hg : d.BddMC g C) (w : Lp ℝ 2 μ) :
    inner ℝ (d.PL g) w = Mn d.m (fun q : d.Q => inner ℝ (d.FL q.out g) w) := by
  have hb : ∀ (w : Lp ℝ 2 μ) (q : d.Q), |inner ℝ (d.FL q.out g) w| ≤ Kμ μ * C * ‖w‖ :=
    fun w q => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (d.norm_FL_le _ hg) (norm_nonneg _))
  refine inner_Rep (fun a b => ?_) (fun c a => ?_) (B := Kμ μ * C) (fun a => ?_) w
  · simp only [inner_add_right]
    exact Mn_add d.hm d.hm1 (hb a) (hb b)
  · simp only [real_inner_smul_right]
    exact Mn_smul d.hm d.hm1 c (hb a)
  · exact Mn_abs_le d.hm d.hm1 (hb a)

lemma KEYW_bdd (hg : d.BddMC g C) {D : X → ℝ} (hD : Measurable D) {M : ℝ}
    (hM : ∀ x, |D x| ≤ M) :
    ∫ x, d.P g x * D x ∂μ = Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ) := by
  have hDL : MemLp D 2 μ := MemLp.of_bound hD.aestronglyMeasurable M
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
  have e1 : inner ℝ (d.PL g) (hDL.toLp D) = ∫ x, d.P g x * D x ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hDL.coeFn_toLp] with x hx
    rw [hx, Real.inner_apply]
    rfl
  have e2 : ∀ l : d.Λ, inner ℝ (d.FL l g) (hDL.toLp D) = ∫ x, d.Fl l g x * D x ∂μ := by
    intro l
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hDL.coeFn_toLp, d.coe_FL l hg] with x hx hx'
    rw [hx, hx', Real.inner_apply]
  rw [← e1, d.inner_PL hg]
  simp only [e2]

lemma setInt_P (hg : d.BddMC g C) {A : Set X} (hA : MeasurableSet A) :
    ∫ x in A, d.P g x ∂μ = Mn d.m (fun q : d.Q => ∫ x in A, d.Fl q.out g x ∂μ) := by
  have := d.KEYW_bdd hg (D := A.indicator 1) (measurable_const.indicator hA) (M := 1)
    (fun x => by by_cases hx : x ∈ A <;> simp [hx])
  simp only [indicator_one_mul', integral_indicator hA] at this
  exact this

lemma integrable_P (g : X × X → ℝ) : Integrable (d.P g) μ :=
  (Lp.memLp _).integrable (by norm_num)

lemma aesm_P (g : X × X → ℝ) : AEStronglyMeasurable (d.P g) μ :=
  Lp.aestronglyMeasurable _

lemma measurable_P (g : X × X → ℝ) : Measurable (d.P g) :=
  (Lp.stronglyMeasurable _).measurable

lemma integrable_Fl (l : d.Λ) (hg : d.BddMC g C) : Integrable (d.Fl l g) μ :=
  Integrable.of_bound (d.aesm_Fl l hg) C (by
    filter_upwards [d.ae_abs_Fl_le l hg] with y hy
    rwa [Real.norm_eq_abs])

lemma abs_setInt_Fl_le (l : d.Λ) (hg : d.BddMC g C) (A : Set X) :
    |∫ x in A, d.Fl l g x ∂μ| ≤ C * μ.real A :=
  abs_setInt_le μ (d.ae_abs_Fl_le l hg) A

lemma P_bound (hg : d.BddMC g C) : ∀ᵐ x ∂μ, |d.P g x| ≤ C := by
  have key : ∀ A, MeasurableSet A → |∫ x in A, d.P g x ∂μ| ≤ C * μ.real A := fun A hA => by
    rw [d.setInt_P hg hA]
    exact Mn_abs_le d.hm d.hm1 (fun q => d.abs_setInt_Fl_le _ hg A)
  have h1 : d.P g ≤ᵐ[μ] fun _ => C :=
    ae_le_of_forall_setIntegral_le (d.integrable_P g) (integrable_const C) (fun A hA _ => by
      rw [setIntegral_const, smul_eq_mul]
      have := key A hA
      linarith [le_abs_self (∫ x in A, d.P g x ∂μ)])
  have h2 : (fun _ => -C) ≤ᵐ[μ] d.P g :=
    ae_le_of_forall_setIntegral_le (integrable_const (-C)) (d.integrable_P g) (fun A hA _ => by
      rw [setIntegral_const, smul_eq_mul]
      have := key A hA
      linarith [neg_abs_le (∫ x in A, d.P g x ∂μ)])
  filter_upwards [h1, h2] with x h1 h2
  exact abs_le.2 ⟨h2, h1⟩

lemma KEYW (hg : d.BddMC g C) {D : X → ℝ} (hD : Measurable D) (hDi : Integrable D μ) :
    ∫ x, d.P g x * D x ∂μ = Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ) := by
  set cl : ℕ → X → ℝ := fun M x => max (min (D x) M) (-M) with hcl
  have hclm : ∀ M, Measurable (cl M) := fun M => (hD.min measurable_const).max measurable_const
  have hclb : ∀ M x, |cl M x| ≤ M := fun M x => abs_le.2 ⟨le_max_right _ _,
    max_le (min_le_right _ _) (by have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith)⟩
  have hcli : ∀ M, Integrable (cl M) μ := fun M =>
    Integrable.of_bound (hclm M).aestronglyMeasurable M
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hclb M x)
  have hconv : Tendsto (fun M : ℕ => 2 * C * ∫ x, |D x - cl M x| ∂μ) atTop (𝓝 0) := by
    simpa using (tendsto_clamp μ hD hDi).const_mul (2 * C)
  have hdiff : ∀ M : ℕ, |(∫ x, d.P g x * D x ∂μ) -
      Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ)| ≤
        2 * C * ∫ x, |D x - cl M x| ∂μ := by
    intro M
    have e1 := d.KEYW_bdd hg (hclm M) (hclb M)
    have h1 := abs_integral_mul_sub_le' μ (d.aesm_P g) (d.P_bound hg) hDi (hcli M)
    have h2 : |Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ) -
        Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * cl M x ∂μ)| ≤
          C * ∫ x, |D x - cl M x| ∂μ :=
      Mn_sub_le d.hm d.hm1 (B := C * ∫ x, |cl M x| ∂μ)
        (fun q => abs_integral_mul_le μ (d.ae_abs_Fl_le _ hg) (hcli M))
        (fun q => abs_integral_mul_sub_le' μ (d.aesm_Fl _ hg) (d.ae_abs_Fl_le _ hg) hDi (hcli M))
    rw [e1] at h1
    have := abs_sub_le (∫ x, d.P g x * D x ∂μ)
      (Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * cl M x ∂μ))
      (Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ))
    rw [abs_sub_comm (Mn d.m _) (Mn d.m _)] at this
    linarith
  have := ge_of_tendsto' hconv hdiff
  have h0 := abs_nonneg ((∫ x, d.P g x * D x ∂μ) -
      Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ))
  have : |(∫ x, d.P g x * D x ∂μ) -
      Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ)| = 0 := le_antisymm this h0
  exact sub_eq_zero.1 (abs_eq_zero.1 this)

/-! ### The axioms of a mean -/
lemma bddMC_add (hg : d.BddMC g C) (hg' : d.BddMC g' C') : d.BddMC (g + g') (C + C') :=
  ⟨hg.1.add hg'.1, add_nonneg hg.2.1 hg'.2.1, fun x hx k hk =>
    (abs_add_le _ _).trans (add_le_add (hg.2.2 x hx k hk) (hg'.2.2 x hx k hk))⟩

lemma bddMC_smul (c : ℝ) (hg : d.BddMC g C) : d.BddMC (c • g) (|c| * C) :=
  ⟨hg.1.const_smul c, mul_nonneg (abs_nonneg c) hg.2.1, fun x hx k hk => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hg.2.2 x hx k hk) (abs_nonneg c)⟩

lemma bddMC_loc (hg : d.BddMC g C) {B : Set X} (hB : MeasurableSet B) :
    d.BddMC (fun p => if p.1 ∈ B then g p else 0) C :=
  ⟨Measurable.ite (hB.preimage measurable_fst) hg.1 measurable_const, hg.2.1, fun x hx k hk => by
    dsimp only
    split_ifs
    · exact hg.2.2 x hx k hk
    · simpa using hg.2.1⟩

lemma bddMC_tr (κ : d.Λ) (hg : d.BddMC g C) : d.BddMC (d.tr κ g) C :=
  ⟨Measurable.ite (d.hX₀.preimage measurable_fst)
    (hg.1.comp (((d.hmeas _ (inv_mem κ.2)).comp measurable_fst).prodMk measurable_snd))
    measurable_const, hg.2.1, fun x hx k hk => by
    simp only [tr, if_pos hx]
    have := hg.2.2 _ (d.smul_mem_X₀ (inv_mem κ.2) hx) (k * κ) (mul_mem hk κ.2)
    simpa [mul_smul] using this⟩

lemma P_add (hg : d.BddMC g C) (hg' : d.BddMC g' C') :
    d.P (g + g') =ᵐ[μ] d.P g + d.P g' := by
  refine ae_eq_of_setInt μ (d.integrable_P _) ((d.integrable_P g).add (d.integrable_P g'))
    fun A hA => ?_
  simp only [Pi.add_apply]
  rw [integral_add (d.integrable_P g).integrableOn (d.integrable_P g').integrableOn,
    d.setInt_P (d.bddMC_add hg hg') hA, d.setInt_P hg hA, d.setInt_P hg' hA,
    ← Mn_add d.hm d.hm1 (fun q => d.abs_setInt_Fl_le _ hg A)
      (fun q => d.abs_setInt_Fl_le _ hg' A)]
  congr 1
  funext q
  rw [← integral_add (d.integrable_Fl _ hg).integrableOn (d.integrable_Fl _ hg').integrableOn]
  exact integral_congr_ae (ae_restrict_of_ae (d.Fl_add _ hg hg'))

lemma P_smul (c : ℝ) (hg : d.BddMC g C) : d.P (c • g) =ᵐ[μ] c • d.P g := by
  refine ae_eq_of_setInt μ (d.integrable_P _) ((d.integrable_P g).smul c) fun A hA => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, d.setInt_P (d.bddMC_smul c hg) hA, d.setInt_P hg hA,
    ← Mn_smul d.hm d.hm1 c (fun q => d.abs_setInt_Fl_le _ hg A)]
  congr 1
  funext q
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [d.Fl_smul q.out c hg] with x hx
  rw [hx]
  rfl

lemma P_zero : d.P (0 : X × X → ℝ) =ᵐ[μ] 0 := by
  have h0 : d.BddMC (0 : X × X → ℝ) 0 := ⟨measurable_const, le_rfl, fun _ _ _ _ => by simp⟩
  have := d.P_smul 0 h0
  rw [zero_smul] at this
  filter_upwards [this] with x hx
  rw [hx]
  simp

lemma P_nonneg (hg : d.BddMC g C) (h0 : ∀ x ∈ d.X₀, ∀ k ∈ d.Λ, 0 ≤ g (x, k • x)) :
    ∀ᵐ x ∂μ, 0 ≤ d.P g x := by
  refine ae_nonneg_of_forall_setIntegral_nonneg (d.integrable_P g) fun A hA _ => ?_
  rw [d.setInt_P hg hA]
  refine Mn_nonneg d.hm d.hm1 (fun q => d.abs_setInt_Fl_le _ hg A) fun q => ?_
  exact integral_nonneg_of_ae (ae_restrict_of_ae (d.Fl_nonneg _ hg h0))

lemma P_one : d.P (1 : X × X → ℝ) =ᵐ[μ] 1 := by
  refine ae_eq_of_setInt μ (d.integrable_P _) (integrable_const 1) fun A hA => ?_
  rw [d.setInt_P d.bddMC_one hA]
  have : ∀ q : d.Q, ∫ x in A, d.Fl q.out (1 : X × X → ℝ) x ∂μ = μ.real A := fun q => by
    rw [integral_congr_ae (ae_restrict_of_ae (d.Fl_one q.out))]
    simp
  simp only [this, Mn_const d.hm d.hm1]
  simp

lemma P_congr (hg : d.BddMC g C) (hg' : d.BddMC g' C') {N : Set X} (hN : μ N = 0)
    (h : ∀ x ∈ d.X₀, x ∉ N → ∀ k ∈ d.Λ, g (x, k • x) = g' (x, k • x)) :
    d.P g =ᵐ[μ] d.P g' := by
  refine ae_eq_of_setInt μ (d.integrable_P _) (d.integrable_P _) fun A hA => ?_
  rw [d.setInt_P hg hA, d.setInt_P hg' hA]
  congr 1
  funext q
  exact integral_congr_ae (ae_restrict_of_ae (d.Fl_congr _ hg hg' hN h))

lemma P_loc (hg : d.BddMC g C) {B : Set X} (hB : MeasurableSet B) :
    d.P (fun p => if p.1 ∈ B then g p else 0) =ᵐ[μ] B.indicator (d.P g) := by
  refine ae_eq_of_setInt μ (d.integrable_P _) ((d.integrable_P g).indicator hB) fun A hA => ?_
  rw [setIntegral_indicator hB, d.setInt_P (d.bddMC_loc hg hB) hA, d.setInt_P hg (hA.inter hB)]
  congr 1
  funext q
  rw [integral_congr_ae (ae_restrict_of_ae (d.Fl_loc q.out hg hB)), setIntegral_indicator hB]

/-- Change of variables along `κ`. -/
lemma cv {κ : G} (hκ : κ ∈ d.Λ) (A : Set X) {u : X → ℝ}
    (hu : AEStronglyMeasurable u μ) :
    ∫ y in A, u (κ • y) ∂μ = ∫ x, u x *
      ((Measure.map (fun y : X => κ • y) (μ.restrict A)).rnDeriv μ x).toReal ∂μ := by
  have hac : Measure.map (fun y : X => κ • y) (μ.restrict A) ≪ μ :=
    (Measure.absolutelyContinuous_of_le
      (Measure.map_mono Measure.restrict_le_self (d.hmeas κ hκ))).trans
      (d.qmp hκ).absolutelyContinuous
  rw [← integral_map (d.hmeas κ hκ).aemeasurable (hu.mono_ac hac), ← integral_rnDeriv_smul hac]
  simp only [smul_eq_mul, mul_comm]

/-- **Translation invariance**: `P (g ∘ κ⁻¹) = (P g) ∘ κ⁻¹`. -/
lemma P_tr (κ : d.Λ) (hg : d.BddMC g C) :
    d.P (d.tr κ g) =ᵐ[μ] fun y => d.P g ((κ : G)⁻¹ • y) := by
  have hq := d.qmp (inv_mem κ.2)
  have hint : Integrable (fun y => d.P g ((κ : G)⁻¹ • y)) μ :=
    Integrable.of_bound ((d.aesm_P g).comp_quasiMeasurePreserving hq) C (by
      filter_upwards [hq.ae (d.P_bound hg)] with y hy
      rwa [Real.norm_eq_abs])
  refine ae_eq_of_setInt μ (d.integrable_P _) hint fun A hA => ?_
  set D : X → ℝ := fun x =>
    ((Measure.map (fun y : X => (κ : G)⁻¹ • y) (μ.restrict A)).rnDeriv μ x).toReal with hD
  have hDm : Measurable D := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hDi : Integrable D μ := Measure.integrable_toReal_rnDeriv
  rw [d.cv (inv_mem κ.2) A (d.aesm_P g)]
  change _ = ∫ x, d.P g x * D x ∂μ
  rw [d.KEYW hg hDm hDi,
    d.setInt_P (d.bddMC_tr κ hg) hA]
  have step1 : ∀ q : d.Q, ∫ x in A, d.Fl q.out (d.tr κ g) x ∂μ =
      ∫ x in A, d.Fl (κ⁻¹ • q).out g ((κ : G)⁻¹ • x) ∂μ := by
    intro q
    simp only [d.Fl_tr]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    have hrep : ((κ⁻¹ * q.out : d.Λ) : d.Q) = (((κ⁻¹ • q).out : d.Λ) : d.Q) := by
      rw [QuotientGroup.out_eq', ← MulAction.Quotient.mk_smul_out]
      rfl
    exact hq.ae_eq (d.Fl_rep hrep hg)
  have step2 : ∀ q : d.Q, ∫ x in A, d.Fl q.out g ((κ : G)⁻¹ • x) ∂μ =
      ∫ x, d.Fl q.out g x * D x ∂μ := fun q => d.cv (inv_mem κ.2) A (d.aesm_Fl _ hg)
  simp only [step1]
  rw [Mn_inv d.hm d.hm1 d.hminv κ (a := fun q : d.Q => ∫ x in A, d.Fl q.out g ((κ : G)⁻¹ • x) ∂μ)
    (fun q => abs_setInt_le μ (hq.ae (d.ae_abs_Fl_le q.out hg)) A)]
  simp only [step2]

/-! ### Invariance under the partial transformations of `R` -/
lemma P_loc_congr (hg : d.BddMC g C) (hg' : d.BddMC g' C') {B : Set X} (hB : MeasurableSet B)
    (h : ∀ x ∈ B, x ∈ d.X₀ → ∀ k ∈ d.Λ, g (x, k • x) = g' (x, k • x)) :
    ∀ᵐ y ∂μ, y ∈ B → d.P g y = d.P g' y := by
  have hc := d.P_congr (d.bddMC_loc hg hB) (d.bddMC_loc hg' hB) (N := ∅) measure_empty
    (fun x hx _ k hk => by
      dsimp only
      split_ifs with hxB
      · exact h x hxB hx k hk
      · rfl)
  filter_upwards [hc, d.P_loc hg hB, d.P_loc hg' hB] with y h1 h2 h3 hy
  rw [h2, h3, Set.indicator_of_mem hy, Set.indicator_of_mem hy] at h1
  exact h1

lemma bddMC_of_isBddMeasOn {f : X × X → ℝ} (hf : IsBddMeasOn d.R f) : ∃ C, d.BddMC f C := by
  obtain ⟨C, hC⟩ := hf.2
  exact ⟨max C 0, hf.1, le_max_right _ _, fun x hx k hk =>
    (hC _ (d.hΛR k hk x hx)).trans (le_max_left _ _)⟩

lemma bddMC_shiftRel (φ : PartialTransformation d.R) {f : X × X → ℝ} (hf : IsBddMeasOn d.R f) :
    ∃ C, d.BddMC (φ.shiftRel f) C := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨max C 0, ?_, le_max_right _ _, fun x hx k hk => ?_⟩
  · rw [shiftRel_eq']
    exact Measurable.ite (φ.measurableSet_cod.preimage measurable_fst)
      (hf.1.comp (((measurable_psi φ).comp measurable_fst).prodMk measurable_snd))
      measurable_const
  · rw [shiftRel_eq']
    dsimp only
    split_ifs with hxc
    · have hR := psi_mem_R φ hxc
      have hψ : psi φ x ∈ d.X₀ := (d.hsat _ hR).2 hx
      obtain ⟨c, hc, hcx⟩ := d.hRC _ hR hψ
      simp only at hcx
      have hR' : (psi φ x, k • x) ∈ d.R := by
        have := d.hΛR (k * c) (mul_mem hk (d.hCΛ hc)) _ hψ
        rwa [mul_smul, hcx] at this
      exact (hC _ hR').trans (le_max_left _ _)
    · simp

theorem P_invariant (φ : PartialTransformation d.R) {f : X × X → ℝ} (hf : IsBddMeasOn d.R f) :
    d.P (φ.shiftRel f) =ᵐ[μ] φ.shiftBase (d.P f) := by
  obtain ⟨C, hfC⟩ := d.bddMC_of_isBddMeasOn hf
  obtain ⟨C', hsC⟩ := d.bddMC_shiftRel φ hf
  let B : G → Set X := fun κ => φ.cod ∩ d.X₀ ∩ {y | d.P f (psi φ y) = d.P f (κ⁻¹ • y)} ∩
    ⋂ c ∈ d.C, {y | f (psi φ y, c • y) = f (κ⁻¹ • y, c • y)}
  have hBm : ∀ κ ∈ d.Λ, MeasurableSet (B κ) := by
    intro κ hκ
    have hκm := d.hmeas _ (inv_mem hκ)
    refine ((φ.measurableSet_cod.inter d.hX₀).inter (measurableSet_eq_fun
      ((d.measurable_P f).comp (measurable_psi φ)) ((d.measurable_P f).comp hκm))).inter
      (MeasurableSet.biInter d.hC fun c hc => measurableSet_eq_fun ?_ ?_)
    · exact hf.1.comp ((measurable_psi φ).prodMk (d.hmeas c (d.hCΛ hc)))
    · exact hf.1.comp (hκm.prodMk (d.hmeas c (d.hCΛ hc)))
  have hi : ∀ᵐ y ∂μ, ∀ κ ∈ d.C, y ∈ B κ → d.P (φ.shiftRel f) y = d.P f (κ⁻¹ • y) := by
    rw [eventually_countable_ball d.hC]
    intro κ hκ
    have h1 := d.P_loc_congr hsC (d.bddMC_tr ⟨κ, d.hCΛ hκ⟩ hfC) (hBm κ (d.hCΛ hκ))
      (fun x hxB hx k hk => by
        rw [shiftRel_eq']
        simp only [tr, if_pos hxB.1.1.1, if_pos hx]
        obtain ⟨c, hc, hcx⟩ := d.hRC _ (d.hΛR k hk x hx) hx
        simp only at hcx
        rw [← hcx]
        exact mem_iInter₂.1 hxB.2 c hc)
    filter_upwards [h1, d.P_tr ⟨κ, d.hCΛ hκ⟩ hfC] with y h1 h2 hy
    rw [h1 hy, h2]
  have h0 : d.BddMC (0 : X × X → ℝ) 0 := ⟨measurable_const, le_rfl, fun _ _ _ _ => by simp⟩
  have hiii := d.P_loc_congr hsC h0 φ.measurableSet_cod.compl (fun x hxB _ k _ => by
    rw [shiftRel_eq']
    simp only [if_neg (show x ∉ φ.cod from hxB)]
    rfl)
  filter_upwards [hi, hiii, d.P_zero, measure_eq_zero_iff_ae_notMem.1 d.hX₀c]
    with y h1 h3 h4 h5
  rw [shiftBase_eq']
  dsimp only
  split_ifs with hy
  · have hX : y ∈ d.X₀ := by simpa using h5
    have hR := psi_mem_R φ hy
    have hψ : psi φ y ∈ d.X₀ := (d.hsat _ hR).2 hX
    obtain ⟨κ, hκ, hκy⟩ := d.hRC _ hR hψ
    simp only at hκy
    have hψy : psi φ y = κ⁻¹ • y := eq_inv_smul_iff.2 hκy
    have hyB : y ∈ B κ := by
      refine ⟨⟨⟨hy, hX⟩, ?_⟩, mem_iInter₂.2 fun c hc => ?_⟩
      · show d.P f (psi φ y) = d.P f (κ⁻¹ • y)
        rw [hψy]
      · show f (psi φ y, c • y) = f (κ⁻¹ • y, c • y)
        rw [hψy]
    rw [h1 κ hκ hyB, hψy]
  · rw [h3 hy, h4]
    rfl

/-- The mean `P` is a left invariant mean on `R`. -/
theorem isLeftInvariantMean : IsLeftInvariantMean μ d.R d.P where
  aemeasurable f _ := (d.aesm_P f).aemeasurable
  congr f g hf hg hfg := by
    obtain ⟨C, hfC⟩ := d.bddMC_of_isBddMeasOn hf
    obtain ⟨C', hgC⟩ := d.bddMC_of_isBddMeasOn hg
    refine d.P_congr hfC hgC hfg fun x hx hxN k hk => ?_
    by_contra hne
    exact hxN ⟨(x, k • x), ⟨hne, d.hΛR k hk x hx⟩, rfl⟩
  add f g hf hg := by
    obtain ⟨C, hfC⟩ := d.bddMC_of_isBddMeasOn hf
    obtain ⟨C', hgC⟩ := d.bddMC_of_isBddMeasOn hg
    exact d.P_add hfC hgC
  smul c f hf := by
    obtain ⟨C, hfC⟩ := d.bddMC_of_isBddMeasOn hf
    exact d.P_smul c hfC
  nonneg f hf hpos := by
    obtain ⟨C, hfC⟩ := d.bddMC_of_isBddMeasOn hf
    exact d.P_nonneg hfC fun x hx k hk => hpos _ (d.hΛR k hk x hx)
  one := d.P_one
  invariant φ f hf := d.P_invariant φ hf

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
theorem isAmenableRel_of_isCoamenable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] {G : Type*} [Group G] [MulAction G X] (Γ Λ : Subgroup G) (hΓΛ : Γ ≤ Λ)
    (hmeas : ∀ g ∈ Λ, Measurable (fun x : X => g • x))
    (hnull : ∀ g ∈ Λ, ∀ s : Set X, μ s = 0 → μ ((fun x : X => g • x) ⁻¹' s) = 0)
    (hco : Monod.IsCoamenable (Γ.subgroupOf Λ))
    (hΓ : Monod.IsAmenableRel μ {p : X × X | ∃ g ∈ Γ, g • p.1 = p.2})
    (R : Set (X × X)) (X₀ : Set X) (hX₀ : MeasurableSet X₀) (hX₀c : μ X₀ᶜ = 0)
    (hsat : ∀ p ∈ R, (p.1 ∈ X₀ ↔ p.2 ∈ X₀))
    (hΛR : ∀ g ∈ Λ, ∀ x ∈ X₀, (x, g • x) ∈ R)
    (C : Set G) (hC : C.Countable) (hCΛ : C ⊆ Λ)
    (hRC : ∀ p ∈ R, p.1 ∈ X₀ → ∃ g ∈ C, g • p.1 = p.2) :
    Monod.IsAmenableRel μ R := by
  obtain ⟨m, hm, hm1, hminv⟩ := hco
  obtain ⟨PΓ, hPΓ⟩ := hΓ
  have hae : ae μ.toFinite = ae μ := ae_toFinite
  have h0 : ∀ s, μ.toFinite s = 0 ↔ μ s = 0 := fun s => by
    rw [measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem, hae]
  let d : Data μ.toFinite G :=
    { Γ := Γ, Λ := Λ, hΓΛ := hΓΛ, hmeas := hmeas,
      hnull := fun g hg s hs => (h0 _).2 (hnull g hg s ((h0 s).1 hs)),
      PΓ := PΓ, hPΓ := lim_of_ae_eq hae.symm hPΓ, R := R, X₀ := X₀, hX₀ := hX₀,
      hX₀c := (h0 _).2 hX₀c, hsat := hsat, hΛR := hΛR, C := C, hC := hC, hCΛ := hCΛ,
      hRC := hRC, m := m, hm := hm, hm1 := hm1, hminv := hminv }
  exact ⟨d.P, lim_of_ae_eq hae d.isLeftInvariantMean⟩

end ThompsonAmenability.M51.PartD
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part D: relative Zimmer (Monod 2023, Proposition 4.7) -/
alias isAmenableRel_of_isCoamenable := ThompsonAmenability.M51.PartD.isAmenableRel_of_isCoamenable

/-! ## Part E1: Thompson's group `F` at non-dyadic points -/

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartE2W
open ThompsonAmenability.M51
/-! # Part E2, from the published `ThompsonOrbit.isAmenableRel_orbit_HRat` -/
theorem isAmenableRel_HRat : Monod.IsAmenableRel Monod.volP1 (orbRel Monod.HRat) :=
  ThompsonOrbit.isAmenableRel_orbit_HRat

end ThompsonAmenability.M51.PartE2W
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part E2: the orbit relation of `H_ℚ(ℤ)` is amenable -/
alias isAmenableRel_HRat := ThompsonAmenability.M51.PartE2W.isAmenableRel_HRat

end ThompsonAmenability.M51
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

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part E3: amenability passes between relations that agree on a conull saturated set -/

/-! ## Assembly -/
alias sigmaFinite_volP1 := ThompsonAmenability.M51.PartA.sigmaFinite_volP1

theorem isAmenableRel_RQ_of_isCoamenable (Λ : Subgroup Hom) (hΓΛ : Monod.HRat ≤ Λ)
    (hΛ : Λ ≤ HB ratSubring Monod.ratPoints) (C : Set Hom) (hC : C.Countable) (hCΛ : C ⊆ Λ)
    (hcut : ∀ x ∈ X0, ∀ g : SLQ, ∃ h ∈ C, h x = Monod.mob g x)
    (hco : Monod.IsCoamenable (Monod.HRat.subgroupOf Λ)) :
    Monod.IsAmenableRel Monod.volP1 RQ := by
  have := sigmaFinite_volP1
  refine isAmenableRel_of_isCoamenable Monod.volP1 Monod.HRat Λ hΓΛ
    (fun g _ => (g : Hom).continuous.measurable)
    (fun g hg s hs => null_preimage_of_mem_HB (hΛ hg) hs)
    hco isAmenableRel_HRat RQ X0 measurableSet_X0 volP1_compl_X0 ?_ ?_ C hC hCΛ ?_
  · rintro ⟨x, y⟩ ⟨g, hg⟩
    simp only at hg ⊢
    rw [← hg]
    exact (mob_mem_X0_iff g x).symm
  · intro g hg x hx
    obtain ⟨k, hk⟩ := exists_mob_of_mem_HB (hΛ hg) hx
    exact ⟨k, by rw [smul_def, hk]⟩
  · rintro ⟨x, y⟩ ⟨g, hg⟩ hx
    simp only at hg hx ⊢
    obtain ⟨h, hh, hhx⟩ := hcut x hx g
    exact ⟨h, hh, by rw [smul_def, hhx, hg]⟩

theorem not_isCoamenable_of (Λ : Subgroup Hom) (hΓΛ : Monod.HRat ≤ Λ)
    (hΛ : Λ ≤ HB ratSubring Monod.ratPoints) (C : Set Hom) (hC : C.Countable) (hCΛ : C ⊆ Λ)
    (hcut : ∀ x ∈ X0, ∀ g : SLQ, ∃ h ∈ C, h x = Monod.mob g x) :
    ¬ Monod.IsCoamenable (Monod.HRat.subgroupOf Λ) := by
  intro hco
  have := countable_ratSubring
  exact Monod.not_isAmenableRel_mob ratSubring dense_ratSubring
    (isAmenableRel_RQ_of_isCoamenable Λ hΓΛ hΛ C hC hCΛ hcut hco)

end ThompsonAmenability.M51
end
end

section
open MeasureTheory Filter Topology
open ThompsonAmenability
open ThompsonAmenability.M51
theorem solution :
    (Monod.HRat ≤ HB ratSubring Monod.ratPoints ∧
      ¬ Monod.IsCoamenable (Monod.HRat.subgroupOf (HB ratSubring Monod.ratPoints))) ∧
    (Monod.HRat ≤ HC1RatRat ∧ ¬ Monod.IsCoamenable (Monod.HRat.subgroupOf HC1RatRat)) := by
  obtain ⟨C, hC, hCH, hcut⟩ := exists_countable_cut
  exact ⟨⟨HRat_le_HB, not_isCoamenable_of _ HRat_le_HB le_rfl C hC (hCH.trans HC1_le_HB) hcut⟩,
    ⟨HRat_le_HC1, not_isCoamenable_of _ HRat_le_HC1 HC1_le_HB C hC hCH hcut⟩⟩
end
