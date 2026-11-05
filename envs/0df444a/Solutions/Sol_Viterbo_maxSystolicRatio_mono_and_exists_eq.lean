-- Prove2me | solution 1 for Viterbo.maxSystolicRatio_mono_and_exists_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:11:36.256759+00:00
-- url     : https://prove2.me/submissions/b91e76df-858c-4da6-95d6-a4432553c85a

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ
import Theorems.Thm_Viterbo_systolicRatio_symplecticPProduct_two
import Theorems.Thm_Viterbo_cEHZ_capacityBall

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-!
# Blueprint: HKO p. 6, `Sys(K²ⁿ)` is monotone in `n`, finite, and attained

`Viterbo.maxSystolicRatio_mono_and_exists_eq`, as a reduction on the two Open siblings
* `exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ` (M10: `c_EHZ` is a capacity on
  convex domains), used through `GoodCap`;
* `systolicRatio_symplecticPProduct_two` (M8: the 2-product formula), for monotonicity.

Route (no Williamson, no John):
* **finite.** A max-volume simplex in `closure A` gives a frame `w` with
  `v + [0, 1/2n]·w ⊆ closure A` and `A ⊆ v + [-1, 1]·w`. With `Ω = gram w` (the matrix
  `ω(wᵢ, wⱼ)`), `Vol(v + [0,1]·w)² = det Ω`. Leibniz gives an entry `|(Ω⁻¹)ₐᵦ| ≥ (det Ω⁻¹ / (2n)!)^{1/2n}`,
  and the symplectic pair dual to `wₐ, wᵦ` puts `A` in a cylinder of capacity `2π / |(Ω⁻¹)ₐᵦ|`.
* **attained.** Normalize a maximizing sequence (translate, scale to `det Ω = 1`); then `Ω⁻¹`, hence
  `Ω`, is bounded; pass to `Ωₖ → Ω_lim`; symplectic maps `Lₖ` make the frames converge
  (`exists_sympL_tendsto`, inverse function theorem for `S ↦ Sᵀ Ω S`); Blaschke selection and a
  homothety sandwich then give a limit body whose ratio is the supremum.
* **mono.** `Sys(A ⊗₂ B) = Sys(A)` for `B` a ball with `c_EHZ(B) = c_EHZ(A)`.
-/
/-- A symplectic capacity agreeing with `c_EHZ` on convex domains (what M10 provides). -/
def GoodCap (n : ℕ) (c : Set (Phase n) → ℝ≥0∞) : Prop :=
  IsSymplecticCapacity n c ∧ ∀ K : Set (Phase n), IsConvexDomain K → c K = cEHZ K

/-- The parallelotope `v + [a, b]·w = {v + ∑ tᵢ wᵢ : a ≤ tᵢ ≤ b}`. -/
def para (v : Phase n) (w : Fin (2 * n) → Phase n) (a b : ℝ) : Set (Phase n) :=
  {z | ∃ t : Fin (2 * n) → ℝ, (∀ i, t i ∈ Icc a b) ∧ z = v + ∑ i, t i • w i}

/-- The skew Gram matrix `ω(wᵢ, wⱼ)` of a frame. -/
noncomputable def gram (w : Fin (2 * n) → Phase n) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  Matrix.of fun i j => omega0 (w i) (w j)

/-- A linear symplectic automorphism. -/
def IsSympL (L : Phase n ≃L[ℝ] Phase n) : Prop :=
  ∀ v w : Phase n, omega0 (L v) (L w) = omega0 v w

theorem exists_goodCap (hn : 1 ≤ n) : ∃ c, GoodCap n c := by
  obtain ⟨⟨c, hc, hcK⟩, -⟩ := exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ n hn
  exact ⟨c, hc, hcK⟩

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Symplectic embeddings and capacities -/
lemma hse_of_subset' {U V : Set (Phase n)} (h : U ⊆ V) : HasSymplecticEmbedding U V :=
  ⟨id, contDiffOn_id, Topology.IsEmbedding.subtypeVal, fun _ hz => h hz, fun _ _ v w => by simp⟩

lemma hse_translate' (U : Set (Phase n)) (d : Phase n) :
    HasSymplecticEmbedding U ((fun z => z + d) '' U) := by
  refine ⟨fun z => z + d, (contDiff_id.add contDiff_const).contDiffOn, ?_, mapsTo_image _ _, ?_⟩
  · exact (Homeomorph.addRight d).isEmbedding.comp Topology.IsEmbedding.subtypeVal
  · intro z _ v w
    rw [fderiv_add_const, fderiv_fun_id]
    rfl

lemma cap_mono' {c : Set (Phase n) → ℝ≥0∞} (hc : IsSymplecticCapacity n c) {U V : Set (Phase n)}
    (h : U ⊆ V) : c U ≤ c V :=
  hc.1 U V (hse_of_subset' h)

lemma cap_translate' {c : Set (Phase n) → ℝ≥0∞} (hc : IsSymplecticCapacity n c) (U : Set (Phase n))
    (d : Phase n) : c ((fun z => z + d) '' U) = c U := by
  apply le_antisymm
  · have := hc.1 _ _ (hse_translate' ((fun z => z + d) '' U) (-d))
    rwa [image_image, show (fun z : Phase n => z + d + -d) = id by funext z; simp,
      image_id] at this
  · exact hc.1 _ _ (hse_translate' U d)

lemma hse_linear (L : Phase n ≃L[ℝ] Phase n) (hL : IsSympL L) (U : Set (Phase n)) :
    HasSymplecticEmbedding U (L '' U) := by
  refine ⟨fun z => L z, L.contDiff.contDiffOn, ?_, mapsTo_image _ _, ?_⟩
  · exact L.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  · intro z _ v w
    rw [L.fderiv]
    exact hL v w

lemma isSympL_symm {L : Phase n ≃L[ℝ] Phase n} (hL : IsSympL L) : IsSympL L.symm := by
  intro v w
  have := hL (L.symm v) (L.symm w)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at this
  exact this.symm

lemma cap_linear {c : Set (Phase n) → ℝ≥0∞} (hc : IsSymplecticCapacity n c)
    (L : Phase n ≃L[ℝ] Phase n) (hL : IsSympL L) (U : Set (Phase n)) : c (L '' U) = c U := by
  apply le_antisymm
  · have := hc.1 _ _ (hse_linear L.symm (isSympL_symm hL) (L '' U))
    rwa [image_image, show (fun z : Phase n => L.symm (L z)) = id by funext z; simp,
      image_id] at this
  · exact hc.1 _ _ (hse_linear L hL U)

lemma image_affine_eq (L : Phase n ≃L[ℝ] Phase n) (b : Phase n) (U : Set (Phase n)) :
    (fun z => L z + b) '' U = (fun z => z + b) '' (L '' U) := by
  rw [image_image]

lemma cap_affine {c : Set (Phase n) → ℝ≥0∞} (hc : IsSymplecticCapacity n c)
    (L : Phase n ≃L[ℝ] Phase n) (hL : IsSympL L) (b : Phase n) (U : Set (Phase n)) :
    c ((fun z => L z + b) '' U) = c U := by
  rw [image_affine_eq, cap_translate' hc, cap_linear hc L hL]

lemma homothety_image_eq (p : Phase n) (t : ℝ) (U : Set (Phase n)) :
    (fun z => p + t • (z - p)) '' U = (fun z => z + (p - t • p)) '' (t • U) := by
  rw [← image_smul, image_image]
  apply image_congr
  intro z _
  simp only [smul_sub]
  abel

lemma cap_homothety {c : Set (Phase n) → ℝ≥0∞} (hc : IsSymplecticCapacity n c) (p : Phase n)
    {t : ℝ} (ht : 0 < t) (U : Set (Phase n)) :
    c ((fun z => p + t • (z - p)) '' U) = ENNReal.ofReal (t ^ 2) * c U := by
  rw [homothety_image_eq, cap_translate' hc, hc.2.1 t ht]

/-! ## Volumes -/
instance instAddHaarPhaseA : (volume : Measure (Phase n)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

lemma finrank_phase : Module.finrank ℝ (Phase n) = 2 * n := by
  rw [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
  ring

lemma volume_translate (d : Phase n) (U : Set (Phase n)) :
    volume ((fun z => z + d) '' U) = volume U := by
  rw [image_add_right]
  exact measure_preimage_add_right _ _ _

lemma volume_smul (t : ℝ) (U : Set (Phase n)) :
    volume (t • U) = ENNReal.ofReal (|t| ^ (2 * n)) * volume U := by
  rw [Measure.addHaar_smul, finrank_phase, abs_pow]

lemma volume_homothety (p : Phase n) {t : ℝ} (ht : 0 < t) (U : Set (Phase n)) :
    volume ((fun z => p + t • (z - p)) '' U) = ENNReal.ofReal (t ^ (2 * n)) * volume U := by
  rw [homothety_image_eq, volume_translate, volume_smul, abs_of_pos ht]

/-- The symplectic form as a bilinear form. -/
noncomputable def omegaB (n : ℕ) : LinearMap.BilinForm ℝ (Phase n) :=
  LinearMap.mk₂ ℝ omega0
    (fun x y z => by simp only [omega0, Prod.fst_add, Prod.snd_add, inner_add_left,
      inner_add_right]; ring)
    (fun a x y => by simp only [omega0, Prod.smul_fst, Prod.smul_snd, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real]; ring)
    (fun x y z => by simp only [omega0, Prod.fst_add, Prod.snd_add, inner_add_left,
      inner_add_right]; ring)
    (fun a x y => by simp only [omega0, Prod.smul_fst, Prod.smul_snd, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real]; ring)

lemma omegaB_apply (x y : Phase n) : omegaB n x y = omega0 x y := rfl

lemma omegaB_nondegenerate : (omegaB n).Nondegenerate := by
  constructor
  · intro x hx
    have h := hx (-x.2, x.1)
    rw [omegaB_apply] at h
    simp only [omega0, inner_neg_left, real_inner_self_eq_norm_sq] at h
    have h1 : ‖x.1‖ = 0 := by nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖, norm_nonneg x.1]
    have h2 : ‖x.2‖ = 0 := by nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖, norm_nonneg x.2]
    exact Prod.ext (norm_eq_zero.1 h1) (norm_eq_zero.1 h2)
  · intro y hy
    have h := hy (y.2, -y.1)
    rw [omegaB_apply] at h
    simp only [omega0, inner_neg_right, real_inner_self_eq_norm_sq] at h
    have h1 : ‖y.1‖ = 0 := by nlinarith [sq_nonneg ‖y.1‖, sq_nonneg ‖y.2‖, norm_nonneg y.1]
    have h2 : ‖y.2‖ = 0 := by nlinarith [sq_nonneg ‖y.1‖, sq_nonneg ‖y.2‖, norm_nonneg y.2]
    exact Prod.ext (norm_eq_zero.1 h1) (norm_eq_zero.1 h2)

lemma abs_det_sympL {L : Phase n ≃L[ℝ] Phase n} (hL : IsSympL L) :
    |LinearMap.det (L : Phase n →ₗ[ℝ] Phase n)| = 1 := by
  let b := Module.finBasis ℝ (Phase n)
  have hcomp : (omegaB n).comp (L : Phase n →ₗ[ℝ] Phase n) (L : Phase n →ₗ[ℝ] Phase n) =
      omegaB n := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp [omegaB_apply, hL x y]
  have hm := LinearMap.BilinForm.toMatrix_comp b b (omegaB n) (L : Phase n →ₗ[ℝ] Phase n)
    (L : Phase n →ₗ[ℝ] Phase n)
  rw [hcomp] at hm
  have hG : (LinearMap.BilinForm.toMatrix b (omegaB n)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 omegaB_nondegenerate
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hd
  have h1 : LinearMap.det (L : Phase n →ₗ[ℝ] Phase n) ^ 2 = 1 := by
    have : (LinearMap.det (L : Phase n →ₗ[ℝ] Phase n) ^ 2 - 1) *
        (LinearMap.BilinForm.toMatrix b (omegaB n)).det = 0 := by linear_combination -hd
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hG
  have h2 : |LinearMap.det (L : Phase n →ₗ[ℝ] Phase n)| ^ 2 = 1 ^ 2 := by rw [sq_abs, h1, one_pow]
  exact (pow_left_inj₀ (abs_nonneg _) zero_le_one two_ne_zero).1 h2

lemma volume_affine (L : Phase n ≃L[ℝ] Phase n) (hL : IsSympL L) (b : Phase n) (U : Set (Phase n)) :
    volume ((fun z => L z + b) '' U) = volume U := by
  rw [image_affine_eq, volume_translate, Measure.addHaar_image_continuousLinearEquiv,
    abs_det_sympL hL, ENNReal.ofReal_one, one_mul]

/-! ## Convex domains -/

lemma cap_eq {c : Set (Phase n) → ℝ≥0∞} (hc : GoodCap n c) {A : Set (Phase n)}
    (hA : IsConvexDomain A) : cEHZ A = c A := (hc.2 A hA).symm

theorem volume_closure_eq {A : Set (Phase n)} (hA : IsConvexDomain A) :
    volume (closure A) = volume A := by
  apply le_antisymm
  · calc volume (closure A) ≤ volume (A ∪ frontier A) := by
          apply measure_mono
          intro x hx
          by_cases h : x ∈ A
          · exact Or.inl h
          · exact Or.inr ⟨hx, fun hi => h (interior_subset hi)⟩
      _ ≤ volume A + volume (frontier A) := measure_union_le _ _
      _ = volume A := by rw [Convex.addHaar_frontier volume hA.2.1, add_zero]
  · exact measure_mono subset_closure

end Viterbo.MS.PartA
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part A: invariance of `Sys` -/
alias volume_closure_eq := Viterbo.MS.PartA.volume_closure_eq

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem isConvexDomain_closure {A : Set (Phase n)} (hA : IsConvexDomain A) :
    IsConvexDomain (closure A) :=
  ⟨hA.1.closure, hA.2.1.closure, hA.2.2.mono (interior_mono subset_closure)⟩

end Viterbo.MS.PartA
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
alias isConvexDomain_closure := Viterbo.MS.PartA.isConvexDomain_closure

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem sys_closure (hn : 1 ≤ n) {c : Set (Phase n) → ℝ≥0∞} (hc : GoodCap n c) {A : Set (Phase n)}
    (hA : IsConvexDomain A) : systolicRatio (closure A) = systolicRatio A := by
  have hcap : c (closure A) = c A := by
    apply le_antisymm
    · obtain ⟨p, hp⟩ := hA.2.2
      have hle : ∀ ε : ℝ, 0 < ε → c (closure A) ≤ ENNReal.ofReal ((1 + ε) ^ 2) * c A := by
        intro ε hε
        rw [← cap_homothety hc.1 p (by linarith : (0 : ℝ) < 1 + ε)]
        apply cap_mono' hc.1
        refine (hA.2.1.closure_subset_image_homothety_interior_of_one_lt hp (1 + ε)
          (by linarith)).trans ?_
        rintro _ ⟨z, hz, rfl⟩
        refine ⟨z, interior_subset hz, ?_⟩
        simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
        abel
      have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) ^ 2) * c A) (𝓝[>] 0)
          (𝓝 (c A)) := by
        have h0 : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) ^ 2)) (𝓝[>] 0) (𝓝 1) := by
          have : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 + ε) ^ 2)) :=
            ENNReal.continuous_ofReal.comp (by fun_prop)
          have h := this.tendsto 0
          simp only [add_zero, one_pow, ENNReal.ofReal_one] at h
          exact h.mono_left nhdsWithin_le_nhds
        simpa using ENNReal.Tendsto.mul_const h0 (Or.inl one_ne_zero)
      exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
    · exact cap_mono' hc.1 subset_closure
  unfold systolicRatio
  rw [cap_eq hc hA, cap_eq hc (isConvexDomain_closure hA), hcap, volume_closure_eq hA]

end Viterbo.MS.PartA
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
alias sys_closure := Viterbo.MS.PartA.sys_closure

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem isConvexDomain_image_sympL (L : Phase n ≃L[ℝ] Phase n) (b : Phase n) {A : Set (Phase n)}
    (hA : IsConvexDomain A) : IsConvexDomain ((fun z => L z + b) '' A) := by
  let H : Phase n ≃ₜ Phase n := L.toHomeomorph.trans (Homeomorph.addRight b)
  have hH : (fun z => L z + b) = H := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [image_affine_eq]
    exact (IsometryEquiv.addRight b).isometry.lipschitz.isBounded_image
      (L.lipschitz.isBounded_image hA.1)
  · rw [image_affine_eq]
    have h1 := hA.2.1.linear_image (L : Phase n →ₗ[ℝ] Phase n)
    have := h1.vadd b
    rwa [← image_vadd, show (fun x : Phase n => b +ᵥ x) = fun z => z + b by
      funext z; rw [vadd_eq_add, add_comm]] at this
  · rw [hH, ← H.image_interior]
    exact hA.2.2.image _

end Viterbo.MS.PartA
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
alias isConvexDomain_image_sympL := Viterbo.MS.PartA.isConvexDomain_image_sympL

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem sys_image_sympL (hn : 1 ≤ n) {c : Set (Phase n) → ℝ≥0∞} (hc : GoodCap n c)
    (L : Phase n ≃L[ℝ] Phase n) (hL : IsSympL L) (b : Phase n) {A : Set (Phase n)}
    (hA : IsConvexDomain A) : systolicRatio ((fun z => L z + b) '' A) = systolicRatio A := by
  unfold systolicRatio
  rw [cap_eq hc hA, cap_eq hc (isConvexDomain_image_sympL L b hA), cap_affine hc.1 L hL,
    volume_affine L hL]

end Viterbo.MS.PartA
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
alias sys_image_sympL := Viterbo.MS.PartA.sys_image_sympL

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
lemma ratio_scale (a b x v : ℝ≥0∞) (k : ℝ≥0∞) (hb0 : b ≠ 0) (hbt : b ≠ ⊤) (_hk : k ≠ 0)
    (_hkt : k ≠ ⊤) : a * x / (k * (b * v)) = a / b * (x / (k * v)) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_left_comm k b v,
    ENNReal.mul_inv (Or.inl hb0) (Or.inl hbt)]
  ring

theorem sys_smul (hn : 1 ≤ n) {c : Set (Phase n) → ℝ≥0∞} (hc : GoodCap n c) {A : Set (Phase n)}
    (hA : IsConvexDomain A) {α : ℝ} (hα : 0 < α) : systolicRatio (α • A) = systolicRatio A := by
  have hαA : α • A = (fun z => (0 : Phase n) + α • (z - 0)) '' A := by
    rw [← image_smul]; simp
  have hD : IsConvexDomain (α • A) := by
    have := isConvexDomain_image_sympL
      (LinearEquiv.smulOfNeZero ℝ (Phase n) α hα.ne').toContinuousLinearEquiv 0 hA
    convert this using 1
    rw [← image_smul]
    simp
  unfold systolicRatio
  rw [cap_eq hc hA, cap_eq hc hD, hc.1.2.1 α hα, volume_smul, abs_of_pos hα, mul_pow,
    ← ENNReal.ofReal_pow (by positivity), ← pow_mul,
    ratio_scale _ _ _ _ _ (by simp; positivity) ENNReal.ofReal_ne_top (by simp [Nat.factorial_ne_zero])
      (ENNReal.natCast_ne_top _), ENNReal.div_self (by simp; positivity) ENNReal.ofReal_ne_top,
    one_mul]

end Viterbo.MS.PartA
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
alias sys_smul := Viterbo.MS.PartA.sys_smul

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartA
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem sys_le_of_sandwich (hn : 1 ≤ n) {c : Set (Phase n) → ℝ≥0∞} (hc : GoodCap n c)
    {K L : Set (Phase n)} (hK : IsConvexDomain K) (hL : IsConvexDomain L) {p : Phase n} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (h₁ : (fun z => p + (1 - ε) • (z - p)) '' L ⊆ K)
    (h₂ : K ⊆ (fun z => p + (1 + ε) • (z - p)) '' L) :
    systolicRatio K ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ (2 * n)) * systolicRatio L := by
  have hm : 0 < 1 - ε := by linarith
  have hp : 0 < 1 + ε := by linarith
  have hcK : c K ≤ ENNReal.ofReal ((1 + ε) ^ 2) * c L := by
    rw [← cap_homothety hc.1 p hp]
    exact cap_mono' hc.1 h₂
  have hvK : ENNReal.ofReal ((1 - ε) ^ (2 * n)) * volume L ≤ volume K := by
    rw [← volume_homothety p hm]
    exact measure_mono h₁
  unfold systolicRatio
  rw [cap_eq hc hK, cap_eq hc hL]
  calc c K ^ n / (n.factorial * volume K)
      ≤ (ENNReal.ofReal ((1 + ε) ^ 2) * c L) ^ n /
          (n.factorial * (ENNReal.ofReal ((1 - ε) ^ (2 * n)) * volume L)) := by
        gcongr
    _ = ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ (2 * n)) * (c L ^ n / (n.factorial * volume L)) := by
        rw [mul_pow, ← ENNReal.ofReal_pow (by positivity), ← pow_mul,
          ratio_scale _ _ _ _ _ (by simp; positivity) ENNReal.ofReal_ne_top (by simp [Nat.factorial_ne_zero])
            (ENNReal.natCast_ne_top _), div_pow,
          ENNReal.ofReal_div_of_pos (by positivity)]

end Viterbo.MS.PartA
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
alias sys_le_of_sandwich := Viterbo.MS.PartA.sys_le_of_sandwich

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartF
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem finrank_phase (n : ℕ) : Module.finrank ℝ (Phase n) = 2 * n := by
  simp [Module.finrank_prod]; ring

/-- Replacing a vector of a frame by a linear combination multiplies `det` by the coefficient. -/
theorem det_update_sum {d : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : Module.Basis (Fin d) ℝ E) (w : Fin d → E) (j : Fin d) (c : Fin d → ℝ) :
    b.det (Function.update w j (∑ i, c i • w i)) = c j * b.det w := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.toMatrix_update]
  rw [← smul_eq_mul, ← Matrix.det_updateCol_sum]
  congr 2
  ext k
  simp [map_sum, Module.Basis.toMatrix_apply]

theorem exists_frame (hn : 1 ≤ n) {A : Set (Phase n)} (hA : IsConvexDomain A) :
    ∃ (v : Phase n) (w : Fin (2 * n) → Phase n), LinearIndependent ℝ w ∧
      A ⊆ para v w (-1) 1 ∧ para v w 0 (1 / (2 * (n : ℝ))) ⊆ closure A := by
  obtain ⟨hbdd, hconv, hint⟩ := hA
  set d := 2 * n with hd
  let b : Module.Basis (Fin d) ℝ (Phase n) := Module.finBasisOfFinrankEq ℝ (Phase n) (finrank_phase n)
  let F : (Fin (d + 1) → Phase n) → ℝ := fun x => |b.det (fun i => x i.succ - x 0)|
  have hFc : Continuous F := by
    refine continuous_abs.comp ?_
    simp only [Module.Basis.det_apply]
    refine Continuous.matrix_det ?_
    refine continuous_pi fun k => continuous_pi fun i => ?_
    simp only [Module.Basis.toMatrix_apply]
    have hc : Continuous (b.coord k) := LinearMap.continuous_of_finiteDimensional _
    exact hc.comp ((continuous_apply _).sub (continuous_apply _))
  set K := closure A with hK
  have hKc : IsCompact K := hbdd.isCompact_closure
  let S : Set (Fin (d + 1) → Phase n) := Set.pi univ fun _ => K
  have hSc : IsCompact S := isCompact_univ_pi fun _ => hKc
  obtain ⟨p, hp⟩ := hint
  have hpA : p ∈ A := interior_subset hp
  have hSne : S.Nonempty := ⟨fun _ => p, fun _ _ => subset_closure hpA⟩
  obtain ⟨x, hxS, hxmax⟩ := hSc.exists_isMaxOn hSne hFc.continuousOn
  -- positivity of the maximum
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  let c : Fin d → ℝ := fun i => r / (2 * (‖b i‖ + 1))
  have hcpos : ∀ i, 0 < c i := fun i => by positivity
  let y : Fin (d + 1) → Phase n := Fin.cons p (fun i => p + c i • b i)
  have hyS : y ∈ S := by
    intro j _
    refine Fin.cases ?_ (fun i => ?_) j
    · exact subset_closure hpA
    · apply subset_closure
      apply interior_subset
      apply hball
      simp only [y, Fin.cons_succ, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos (hcpos i)]
      have h1 : 0 ≤ ‖b i‖ := norm_nonneg _
      calc r / (2 * (‖b i‖ + 1)) * ‖b i‖ ≤ r / (2 * (‖b i‖ + 1)) * (‖b i‖ + 1) := by
            gcongr; linarith
        _ = r / 2 := by field_simp
        _ < r := by linarith
  have hFy : F y ≠ 0 := by
    have : (fun i => y i.succ - y 0) = fun i => c i • b i := by
      funext i; simp [y]
    simp only [F, this, AlternatingMap.map_smul_univ, Module.Basis.det_self, smul_eq_mul, mul_one]
    exact abs_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => (hcpos i).ne')
  have hFx : F x ≠ 0 := by
    intro h0
    have := hxmax hyS
    simp only [mem_ofPred_eq] at this
    have hpos : 0 < F y := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hFy)
    linarith
  set w : Fin d → Phase n := fun i => x i.succ - x 0 with hw
  have hdet : b.det w ≠ 0 := fun h => hFx (by simp [F, ← hw, h])
  obtain ⟨hli, hspan⟩ := (b.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨x 0, w, hli, ?_, ?_⟩
  · intro z hz
    let B := Module.Basis.mk hli hspan.ge
    let l := B.repr (z - x 0)
    have hsum : ∑ i, l i • w i = z - x 0 := by
      have hB : ∀ i, B i = w i := fun i => by simp [B]
      calc ∑ i, l i • w i = ∑ i, l i • B i := by simp only [hB]
        _ = z - x 0 := B.sum_repr _
    refine ⟨fun i => l i, fun i => ?_, by rw [hsum]; abel⟩
    -- replace vertex i.succ by z
    let x' := Function.update x i.succ z
    have hx'S : x' ∈ S := by
      intro j _
      by_cases hj : j = i.succ
      · subst hj; simpa [x'] using subset_closure hz
      · simp only [x', Function.update_of_ne hj]; exact hxS j (mem_univ _)
    have hle := hxmax hx'S
    simp only [mem_ofPred_eq] at hle
    have hw' : (fun k => x' k.succ - x' 0) = Function.update w i (∑ k, l k • w k) := by
      funext k
      have h0 : x' 0 = x 0 := Function.update_of_ne (Fin.succ_ne_zero i).symm _ _
      by_cases hk : k = i
      · subst hk; simp [x', h0, hsum]
      · rw [Function.update_of_ne hk]
        simp [x', h0, Function.update_of_ne (fun h => hk (Fin.succ_injective _ h)), w]
    have hFx' : F x' = |l i| * F x := by
      simp only [F, hw', det_update_sum, abs_mul, w]
    rw [hFx'] at hle
    have hFxpos : 0 < F x := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hFx)
    have : |l i| ≤ 1 := by nlinarith
    exact ⟨by linarith [neg_abs_le (l i)], le_trans (le_abs_self _) this⟩
  · rintro z ⟨t, ht, rfl⟩
    have hKconv : Convex ℝ K := hconv.closure
    have hdpos : (0 : ℝ) < d := by simp [hd]; omega
    have hts : ∑ i, t i ≤ 1 := by
      calc ∑ i, t i ≤ ∑ _i : Fin d, 1 / (2 * (n : ℝ)) := Finset.sum_le_sum fun i _ => (ht i).2
        _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hd]
          push_cast
          field_simp
    let μ : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, t i) t
    have hμ0 : ∀ j ∈ (Finset.univ : Finset (Fin (d + 1))), 0 ≤ μ j := by
      intro j _
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [μ]; linarith
      · simp [μ]; exact (ht i).1
    have hμ1 : ∑ j, μ j = 1 := by
      simp [μ, Fin.sum_univ_succ]; ring
    have hmem := hKconv.sum_mem hμ0 hμ1 (fun j _ => hxS j (mem_univ _))
    convert hmem using 1
    simp only [Fin.sum_univ_succ, μ, Fin.cons_zero, Fin.cons_succ, w, smul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul, one_smul]
    abel

end Viterbo.MS.PartF
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part F: a frame from a max-volume simplex -/
alias exists_frame := Viterbo.MS.PartF.exists_frame

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartV
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise Matrix
open Module
variable {n : ℕ}
instance instAddHaarPhase : (volume : Measure (Phase n)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

theorem finrank_phase : Module.finrank ℝ (Phase n) = 2 * n := by
  simp [Module.finrank_prod, two_mul]

theorem para_eq_image (v : Phase n) (w : Fin (2 * n) → Phase n) {a b : ℝ} (hab : a ≤ b) :
    para v w a b =
      (fun s => (v + ∑ i, a • w i) + s) '' ((b - a) • para (0 : Phase n) w 0 1) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases hab.eq_or_lt with h | h
    · subst h
      refine ⟨0, ⟨0, ⟨0, fun i => by simp, by simp⟩, by simp⟩, ?_⟩
      have : ∀ i, t i = a := fun i => le_antisymm (ht i).2 (ht i).1
      simp [this]
    · have hba : 0 < b - a := sub_pos.mpr h
      refine ⟨∑ i, (t i - a) • w i, ⟨∑ i, ((t i - a) / (b - a)) • w i,
        ⟨fun i => (t i - a) / (b - a), fun i => ?_, by simp⟩, ?_⟩, ?_⟩
      · constructor
        · exact div_nonneg (by linarith [(ht i).1]) hba.le
        · rw [div_le_one hba]; linarith [(ht i).2]
      · simp only [Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; field_simp
      · simp only [sub_smul, Finset.sum_sub_distrib]
        abel
  · rintro ⟨_, ⟨y, ⟨s, hs, rfl⟩, rfl⟩, rfl⟩
    refine ⟨fun i => a + (b - a) * s i, fun i => ⟨?_, ?_⟩, ?_⟩
    · nlinarith [(hs i).1, (hs i).2]
    · nlinarith [(hs i).1, (hs i).2]
    · simp only [zero_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
      abel

theorem volume_para (v : Phase n) (w : Fin (2 * n) → Phase n) {a b : ℝ} (hab : a ≤ b) :
    volume (para v w a b) = ENNReal.ofReal ((b - a) ^ (2 * n)) * volume (para 0 w 0 1) := by
  rw [para_eq_image v w hab, Set.image_add_left, measure_preimage_add, Measure.addHaar_smul,
    finrank_phase, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hab) _)]

end Viterbo.MS.PartV
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part V: volume of a parallelotope -/
alias volume_para := Viterbo.MS.PartV.volume_para

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartV
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise Matrix
open Module
variable {n : ℕ}
/-- The standard symplectic matrix in block form. -/
def Jstd (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem det_Jstd : (Jstd n).det = 1 := by
  have h : Jstd n = Matrix.fromBlocks 1 0 (-1) 1 * Matrix.fromBlocks 1 1 0 1 *
      Matrix.fromBlocks 1 0 (-1) 1 := by
    simp [Jstd, Matrix.fromBlocks_multiply]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁]
  simp

/-- The product basis of `Phase n`. -/
noncomputable def stdB (n : ℕ) : Basis (Fin n ⊕ Fin n) ℝ (Phase n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.prod (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

def sig (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (two_mul n).symm)

noncomputable def stdB' (n : ℕ) : Basis (Fin (2 * n)) ℝ (Phase n) := (stdB n).reindex (sig n)

theorem stdB'_addHaar : (stdB' n).addHaar = volume := by
  rw [stdB', Basis.addHaar_reindex, stdB, Basis.prod_addHaar, OrthonormalBasis.addHaar_eq_volume,
    Measure.volume_eq_prod]

theorem para_eq_parallelepiped (w : Fin (2 * n) → Phase n) :
    para 0 w 0 1 = parallelepiped w := by
  ext z
  simp only [para, parallelepiped, mem_ofPred_eq, mem_image, zero_add, Set.mem_Icc,
    Pi.le_def, Pi.zero_apply, Pi.one_apply]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ⟨fun i => (ht i).1, fun i => (ht i).2⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, fun i => ⟨ht.1 i, ht.2 i⟩, rfl⟩

theorem gram_eq (w : Fin (2 * n) → Phase n) :
    gram w = ((stdB' n).toMatrix w)ᵀ * Matrix.reindex (sig n) (sig n) (Jstd n) *
      (stdB' n).toMatrix w := by
  ext j k
  simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Basis.toMatrix_apply, stdB', Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [← (sig n).sum_comp]
  simp only [Equiv.symm_apply_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← (sig n).sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Jstd, stdB,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply]
  simp [omega0, PiLp.inner_apply, mul_comm]
  ring

theorem volume_para_sq {w : Fin (2 * n) → Phase n} (hw : LinearIndependent ℝ w) :
    volume (para 0 w 0 1) ^ 2 = ENNReal.ofReal (gram w).det ∧ 0 < (gram w).det := by
  have hdet : (gram w).det = ((stdB' n).det w) ^ 2 := by
    rw [gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_reindex_self,
      det_Jstd, Basis.det_apply]
    ring
  refine ⟨?_, ?_⟩
  · rw [para_eq_parallelepiped, ← stdB'_addHaar, MeasureTheory.Measure.addHaar_parallelepiped,
      hdet, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  · rw [hdet]
    have hspan := hw.span_eq_top_of_card_eq_finrank' (by rw [finrank_phase]; simp)
    have hu := ((stdB' n).is_basis_iff_det).mp ⟨hw, hspan⟩
    have h0 : (stdB' n).det w ≠ 0 := hu.ne_zero
    positivity

end Viterbo.MS.PartV
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
alias volume_para_sq := Viterbo.MS.PartV.volume_para_sq

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartY
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise ContDiff
variable {n : ℕ}
/-! ## Bilinearity of `ω₀` -/
lemma om_add_left (x x' y : Phase n) : omega0 (x + x') y = omega0 x y + omega0 x' y := by
  simp only [omega0, Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right]; ring

lemma om_add_right (x y y' : Phase n) : omega0 x (y + y') = omega0 x y + omega0 x y' := by
  simp only [omega0, Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right]; ring

lemma om_smul_left (r : ℝ) (x y : Phase n) : omega0 (r • x) y = r * omega0 x y := by
  simp only [omega0, Prod.smul_fst, Prod.smul_snd, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]; ring

lemma om_smul_right (r : ℝ) (x y : Phase n) : omega0 x (r • y) = r * omega0 x y := by
  simp only [omega0, Prod.smul_fst, Prod.smul_snd, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]; ring

lemma om_anti (x y : Phase n) : omega0 y x = - omega0 x y := by
  simp only [omega0]; ring

lemma om_self (x : Phase n) : omega0 x x = 0 := by
  have := om_anti x x; linarith

lemma om_sub_right (x y y' : Phase n) : omega0 x (y - y') = omega0 x y - omega0 x y' := by
  rw [sub_eq_add_neg, om_add_right, ← neg_one_smul ℝ y', om_smul_right]; ring

noncomputable def omL : Phase n →ₗ[ℝ] Phase n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ omega0 om_add_left om_smul_left om_add_right om_smul_right

lemma omL_apply (x y : Phase n) : omL x y = omega0 x y := rfl

lemma om_sum_left {ι : Type*} (s : Finset ι) (f : ι → Phase n) (y : Phase n) :
    omega0 (∑ i ∈ s, f i) y = ∑ i ∈ s, omega0 (f i) y := by
  simp only [← omL_apply, map_sum, LinearMap.sum_apply]

lemma om_sum_right {ι : Type*} (s : Finset ι) (f : ι → Phase n) (x : Phase n) :
    omega0 x (∑ i ∈ s, f i) = ∑ i ∈ s, omega0 x (f i) := by
  simp only [← omL_apply, map_sum]

/-- Nondegeneracy. -/
lemma om_J (x : Phase n) : omega0 x (-x.2, x.1) = ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 := by
  simp only [omega0, inner_neg_left, real_inner_self_eq_norm_sq]; ring

lemma exists_om_ne {x : Phase n} (hx : x ≠ 0) : ∃ a, omega0 x a ≠ 0 := by
  refine ⟨(-x.2, x.1), ?_⟩
  rw [om_J]
  intro h
  apply hx
  have h1 : ‖x.1‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖]
  have h2 : ‖x.2‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2‖]
  exact Prod.ext (by simpa using h1) (by simpa using h2)

/-! ## Symplectic linear automorphisms -/
def Symp (M : Phase n ≃L[ℝ] Phase n) : Prop := ∀ x y, omega0 (M x) (M y) = omega0 x y

lemma Symp.trans {M N : Phase n ≃L[ℝ] Phase n} (hM : Symp M) (hN : Symp N) : Symp (M.trans N) := by
  intro x y; simp only [ContinuousLinearEquiv.trans_apply]; exact (hN _ _).trans (hM _ _)

/-- The transvection `x ↦ x + c ω(x, y) y`. -/
noncomputable def transvL (y : Phase n) (c : ℝ) : Phase n →ₗ[ℝ] Phase n where
  toFun x := x + (c * omega0 x y) • y
  map_add' x x' := by rw [om_add_left, mul_add, add_smul]; abel
  map_smul' r x := by
    rw [om_smul_left, smul_add, smul_smul, RingHom.id_apply]; congr 2; ring

lemma transvL_apply (y : Phase n) (c : ℝ) (x : Phase n) :
    transvL y c x = x + (c * omega0 x y) • y := rfl

lemma transvL_inv (y : Phase n) (c : ℝ) (x : Phase n) : transvL y (-c) (transvL y c x) = x := by
  simp only [transvL_apply, om_add_left, om_smul_left, om_self]
  rw [add_assoc, ← add_smul]; simp

noncomputable def transv (y : Phase n) (c : ℝ) : Phase n ≃L[ℝ] Phase n :=
  (LinearEquiv.ofLinearMap (transvL y c) (transvL y (-c))
    (LinearMap.ext fun x => by
      have := transvL_inv y (-c) x; rw [neg_neg] at this; exact this)
    (LinearMap.ext fun x => transvL_inv y c x)).toContinuousLinearEquiv

lemma transv_apply (y : Phase n) (c : ℝ) (x : Phase n) :
    transv y c x = x + (c * omega0 x y) • y := rfl

lemma transv_symp (y : Phase n) (c : ℝ) : Symp (transv y c) := by
  intro x x'
  simp only [transv_apply, om_add_left, om_add_right, om_smul_left, om_smul_right, om_self]
  rw [om_anti y x']; ring

lemma exists_transv {x x' : Phase n} (h : omega0 x x' ≠ 0) :
    ∃ M : Phase n ≃L[ℝ] Phase n, Symp M ∧ M x = x' ∧ ∀ z, omega0 z (x' - x) = 0 → M z = z := by
  refine ⟨transv (x' - x) (omega0 x x')⁻¹, transv_symp _ _, ?_, ?_⟩
  · rw [transv_apply, om_sub_right, om_self, sub_zero, inv_mul_cancel₀ h, one_smul]; abel
  · intro z hz; rw [transv_apply, hz]; simp

lemma exists_symp_map {x x' : Phase n} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ∃ M : Phase n ≃L[ℝ] Phase n, Symp M ∧ M x = x' := by
  -- an intermediate vector `x''` with `ω(x, x'') ≠ 0 ≠ ω(x'', x')`
  have key : ∀ x'' : Phase n, omega0 x x'' ≠ 0 → omega0 x'' x' ≠ 0 →
      ∃ M : Phase n ≃L[ℝ] Phase n, Symp M ∧ M x = x' := by
    intro x'' h1 h2
    obtain ⟨M₁, hM₁, e₁, -⟩ := exists_transv h1
    obtain ⟨M₂, hM₂, e₂, -⟩ := exists_transv h2
    exact ⟨M₁.trans M₂, hM₁.trans hM₂, by simp [e₁, e₂]⟩
  by_cases h : omega0 x x' ≠ 0
  · obtain ⟨M, hM, e, -⟩ := exists_transv h; exact ⟨M, hM, e⟩
  obtain ⟨a, ha⟩ := exists_om_ne hx
  obtain ⟨b', hb'⟩ := exists_om_ne hx'
  have hb : omega0 (-b') x' ≠ 0 := by
    rw [om_anti, ← neg_one_smul ℝ b', om_smul_right]; simpa using hb'
  by_cases h1 : omega0 a x' ≠ 0
  · exact key a ha h1
  by_cases h2 : omega0 x (-b') ≠ 0
  · exact key (-b') h2 hb
  push Not at h1 h2
  refine key (a + -b') ?_ ?_
  · rw [om_add_right, h2, add_zero]; exact ha
  · rw [om_add_left, h1, zero_add]; exact hb

/-! ## The standard pair -/
noncomputable def eS (i0 : Fin n) : Phase n := (EuclideanSpace.single i0 1, 0)

noncomputable def fS (i0 : Fin n) : Phase n := (0, EuclideanSpace.single i0 1)

lemma om_fS (i0 : Fin n) (z : Phase n) : omega0 z (fS i0) = z.1 i0 := by
  simp [omega0, fS, EuclideanSpace.inner_single_right]

lemma om_eS (i0 : Fin n) (z : Phase n) : omega0 (eS i0) z = z.2 i0 := by
  simp [omega0, eS, EuclideanSpace.inner_single_left]

lemma om_eS_fS (i0 : Fin n) : omega0 (eS i0) (fS i0) = 1 := by
  rw [om_eS]; simp [fS]

lemma om_fS_fS (i0 : Fin n) : omega0 (fS i0) (fS i0) = 0 := om_self _

lemma eS_ne (i0 : Fin n) : eS i0 ≠ 0 := by
  intro h
  have := congrArg (fun z : Phase n => z.1 i0) h
  simp [eS] at this

lemma exists_symp_pair (i0 : Fin n) {u v : Phase n} (huv : omega0 u v = 1) :
    ∃ M : Phase n ≃L[ℝ] Phase n, Symp M ∧ M u = eS i0 ∧ M v = fS i0 := by
  have hu : u ≠ 0 := by
    rintro rfl; simp [omega0] at huv
  obtain ⟨M₁, hM₁, e₁⟩ := exists_symp_map hu (eS_ne i0)
  set v' := M₁ v with hv'
  have hev : omega0 (eS i0) v' = 1 := by rw [← e₁, hv', hM₁, huv]
  -- now move `v'` to `fS` fixing `eS`
  have step : ∃ M₂ : Phase n ≃L[ℝ] Phase n, Symp M₂ ∧ M₂ (eS i0) = eS i0 ∧ M₂ v' = fS i0 := by
    by_cases h : omega0 v' (fS i0) ≠ 0
    · obtain ⟨M, hM, e, hfix⟩ := exists_transv h
      refine ⟨M, hM, hfix _ ?_, e⟩
      rw [om_sub_right, om_eS_fS, hev, sub_self]
    push Not at h
    have h1 : omega0 v' (eS i0 + fS i0) ≠ 0 := by
      rw [om_add_right, h, add_zero, om_anti, hev]; norm_num
    have h2 : omega0 (eS i0 + fS i0) (fS i0) ≠ 0 := by
      rw [om_add_left, om_eS_fS, om_fS_fS]; norm_num
    obtain ⟨Ma, hMa, ea, hfa⟩ := exists_transv h1
    obtain ⟨Mb, hMb, eb, hfb⟩ := exists_transv h2
    refine ⟨Ma.trans Mb, hMa.trans hMb, ?_, by simp [ea, eb]⟩
    have hA : Ma (eS i0) = eS i0 := hfa _ (by
      rw [om_sub_right, om_add_right, om_self, om_eS_fS, hev]; norm_num)
    have hB : Mb (eS i0) = eS i0 := hfb _ (by
      rw [om_sub_right, om_add_right, om_self, om_eS_fS]; norm_num)
    simp [hA, hB]
  obtain ⟨M₂, hM₂, hfix, e₂⟩ := step
  exact ⟨M₁.trans M₂, hM₁.trans hM₂, by simp [e₁, hfix], by simp [← hv', e₂]⟩

/-! ## Dual vectors of a frame -/
noncomputable def dualV (w : Fin (2 * n) → Phase n) (N : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (a : Fin (2 * n)) : Phase n :=
  ∑ j, N j a • w j

lemma om_comb_dual (w : Fin (2 * n) → Phase n) {N : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ}
    (hN : gram w * N = 1) (t : Fin (2 * n) → ℝ) (a : Fin (2 * n)) :
    omega0 (∑ i, t i • w i) (dualV w N a) = t a := by
  have h : ∀ i, ∑ j, N j a * omega0 (w i) (w j) = (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) i a := by
    intro i
    rw [← hN, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gram, Matrix.of_apply, mul_comm]
  calc omega0 (∑ i, t i • w i) (dualV w N a)
      = ∑ i, t i * ∑ j, N j a * omega0 (w i) (w j) := by
        rw [om_sum_left]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [om_smul_left, dualV, om_sum_right]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [om_smul_right]
    _ = ∑ i, t i * (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) i a :=
        Finset.sum_congr rfl fun i _ => by rw [h i]
    _ = t a := by simp [Matrix.one_apply]

/-! ## Cylinders -/
lemma smul_capacityCylinder' {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    α • capacityCylinder n c = capacityCylinder n (α ^ 2 * c) := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hα]
  simp only [capacityCylinder, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply,
    smul_eq_mul, mul_pow, inv_pow]
  have h2 : 0 < α ^ 2 := by positivity
  refine forall_congr' fun i => imp_congr_right fun _ => ?_
  rw [← mul_add, ← mul_assoc, mul_comm Real.pi, mul_assoc, inv_mul_lt_iff₀ h2]

lemma cap_cylinder {c : Set (Phase n) → ℝ≥0∞} (hc : IsSymplecticCapacity n c) {C : ℝ} (hC : 0 < C) :
    c (capacityCylinder n C) = ENNReal.ofReal C := by
  set α := Real.sqrt (C / Real.pi)
  have hα : 0 < α := Real.sqrt_pos.mpr (div_pos hC Real.pi_pos)
  have hα2 : α ^ 2 * Real.pi = C := by
    rw [Real.sq_sqrt (div_pos hC Real.pi_pos).le]; field_simp
  have := hc.2.1 α hα (capacityCylinder n Real.pi)
  rw [smul_capacityCylinder' hα.ne', hα2, hc.2.2.2, ← ENNReal.ofReal_mul (by positivity), hα2]
    at this
  exact this

/-! ## Part Y -/
theorem cap_le_of_subset_para (hn : 1 ≤ n) {c : Set (Phase n) → ℝ≥0∞} (hc : IsSymplecticCapacity n c)
    {A : Set (Phase n)} {v : Phase n} {w : Fin (2 * n) → Phase n} (hw : LinearIndependent ℝ w)
    (hA : A ⊆ para v w (-1) 1) {a b : Fin (2 * n)} (hg : (gram w)⁻¹ a b ≠ 0) :
    c A ≤ ENNReal.ofReal (2 * Real.pi / |(gram w)⁻¹ a b|) := by
  set N := (gram w)⁻¹ with hNdef
  have hdet : IsUnit (gram w).det := by
    by_contra h
    exact hg (by rw [hNdef, Matrix.nonsing_inv_apply_not_isUnit _ h]; rfl)
  have hN : gram w * N = 1 := Matrix.mul_nonsing_inv _ hdet
  have hdual : ∀ (t : Fin (2 * n) → ℝ) (k : Fin (2 * n)),
      omega0 (∑ i, t i • w i) (dualV w N k) = t k := fun t k => om_comb_dual w hN t k
  set g := N a b with hgdef
  have hgab : omega0 (dualV w N b) (dualV w N a) = g := hdual (fun j => N j b) a
  have hgpos : 0 < |g| := abs_pos.mpr hg
  set s : ℝ := (Real.sqrt |g|)⁻¹ with hsdef
  have hs : s ^ 2 = |g|⁻¹ := by rw [hsdef, inv_pow, Real.sq_sqrt hgpos.le]
  have hs0 : s ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hgpos).ne'
  set V := s • dualV w N a with hV
  set U := (g * s)⁻¹ • dualV w N b with hU
  have hUV : omega0 U V = 1 := by
    rw [hU, hV, om_smul_left, om_smul_right, hgab]; field_simp
  let i0 : Fin n := ⟨0, hn⟩
  obtain ⟨M, hM, hMU, hMV⟩ := exists_symp_pair i0 hUV
  have h1 : ∀ x, (M x).1 i0 = omega0 x V := fun x => by rw [← om_fS, ← hMV, hM]
  have h2 : ∀ x, (M x).2 i0 = omega0 U x := fun x => by rw [← om_eS, ← hMU, hM]
  have hbound : ∀ x ∈ A,
      Real.pi * ((M (x - v)).1 i0 ^ 2 + (M (x - v)).2 i0 ^ 2) ≤ 2 * Real.pi / |g| := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hA hx
    have hd : v + ∑ i, t i • w i - v = ∑ i, t i • w i := by abel
    rw [h1, h2, hd, hV, hU, om_smul_right, om_smul_left, hdual, om_anti, hdual]
    have hsq : ∀ k, t k ^ 2 ≤ 1 := fun k => by
      rw [sq_le_one_iff_abs_le_one, abs_le]; exact ⟨(ht k).1, (ht k).2⟩
    have e1 : (s * t a) ^ 2 = |g|⁻¹ * t a ^ 2 := by rw [mul_pow, hs]
    have e2 : ((g * s)⁻¹ * -t b) ^ 2 = |g|⁻¹ * t b ^ 2 := by
      rw [mul_pow, inv_pow, mul_pow, hs, ← sq_abs g, neg_sq]; field_simp
    rw [e1, e2, div_eq_mul_inv]
    have hgi : 0 < |g|⁻¹ := inv_pos.mpr hgpos
    have := mul_pos Real.pi_pos hgi
    nlinarith [mul_nonneg this.le (sub_nonneg.mpr (hsq a)),
      mul_nonneg this.le (sub_nonneg.mpr (hsq b))]
  have hcyl : ∀ C : ℝ, 2 * Real.pi / |g| < C → c A ≤ ENNReal.ofReal C := by
    intro C hC
    have hC0 : 0 < C := lt_of_le_of_lt (by positivity) hC
    rw [← cap_cylinder hc hC0]
    apply hc.1
    refine ⟨fun x => M x + -(M v), (M.contDiff.add contDiff_const).contDiffOn, ?_, ?_, ?_⟩
    · have := (M.toHomeomorph.trans (Homeomorph.addRight (-(M v)))).isEmbedding.comp
        (IsEmbedding.subtypeVal (p := fun x => x ∈ A))
      exact this
    · intro x hx i hi
      have hi' : i = i0 := Fin.ext hi
      subst hi'
      have := hbound x hx
      rw [map_sub] at this
      show Real.pi * ((M x + -M v).1 i0 ^ 2 + (M x + -M v).2 i0 ^ 2) < C
      rw [← sub_eq_add_neg]; linarith
    · intro z _ v1 v2
      rw [fderiv_add_const, ContinuousLinearEquiv.fderiv]
      exact hM v1 v2
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have := hcyl (2 * Real.pi / |g| + ε) (by simp [hε])
  rwa [ENNReal.ofReal_add (by positivity) ε.coe_nonneg, ENNReal.ofReal_coe_nnreal] at this

end Viterbo.MS.PartY
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part Y: a cylinder around a parallelotope -/
alias cap_le_of_subset_para := Viterbo.MS.PartY.cap_le_of_subset_para

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartN
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part H: Leibniz bound -/
theorem abs_det_le_of_entries {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) {m : ℝ}
    (hm : ∀ i j, |M i j| ≤ m) : |M.det| ≤ d.factorial * m ^ d := by
  rw [Matrix.det_apply]
  calc |∑ σ : Equiv.Perm (Fin d), Equiv.Perm.sign σ • ∏ i, M (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin d), |Equiv.Perm.sign σ • ∏ i, M (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), m ^ d := by
        apply Finset.sum_le_sum
        intro σ _
        have h1 : |Equiv.Perm.sign σ • ∏ i, M (σ i) i| = ∏ i, |M (σ i) i| := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
            simp [h, Finset.abs_prod]
        rw [h1]
        calc ∏ i, |M (σ i) i| ≤ ∏ _i : Fin d, m :=
              Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hm _ _)
          _ = m ^ d := by simp
    _ = d.factorial * m ^ d := by
        simp [Finset.card_univ, Fintype.card_perm]

theorem exists_det_le {d : ℕ} (hd : 0 < d) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ a b : Fin d, |M.det| ≤ d.factorial * |M a b| ^ d := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_max (fun p : Fin d × Fin d => |M p.1 p.2|)
  exact ⟨p.1, p.2, abs_det_le_of_entries M fun i j => hp (i, j)⟩

end Viterbo.MS.PartN
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part H: Leibniz bound -/

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartN
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Volume lower bound from an inner parallelotope -/
theorem vol_para_unit_eq {w : Fin (2 * n) → Phase n} (hw : LinearIndependent ℝ w) :
    volume (para 0 w 0 1) = ENNReal.ofReal (Real.sqrt (gram w).det) := by
  have h := (volume_para_sq hw).1
  have hD := (volume_para_sq hw).2
  have h2 : ENNReal.ofReal (Real.sqrt (gram w).det) ^ 2 = ENNReal.ofReal (gram w).det := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hD.le]
  exact (ENNReal.pow_right_strictMono (n := 2) (by norm_num)).injective (h.trans h2.symm)

theorem vol_lower (hn : 1 ≤ n) {A : Set (Phase n)} (hA : IsConvexDomain A) {v : Phase n}
    {w : Fin (2 * n) → Phase n} (hw : LinearIndependent ℝ w)
    (hsub : para v w 0 (1 / (2 * (n : ℝ))) ⊆ closure A) :
    ENNReal.ofReal ((1 / (2 * (n : ℝ))) ^ (2 * n) * Real.sqrt (gram w).det) ≤ volume A := by
  have hpos : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)) := by positivity
  rw [← volume_closure_eq hA]
  refine le_trans ?_ (measure_mono hsub)
  rw [volume_para v w hpos, vol_para_unit_eq hw, sub_zero,
    ENNReal.ofReal_mul (pow_nonneg hpos _)]

theorem vol_lt_top {A : Set (Phase n)} (hA : IsConvexDomain A) : volume A < ⊤ :=
  hA.1.measure_lt_top

/-! ## Part S1: `Sys` is bounded -/
theorem real_ineq {F t : ℝ} (hF : 1 ≤ F) (ht : 0 < t) (h : 1 ≤ F * t ^ 2) : 1 ≤ F * t := by
  rcases le_or_gt 1 t with h1 | h1
  · nlinarith
  · nlinarith

theorem systolicRatio_le_const (hn : 1 ≤ n) :
    ∃ C : ℝ, ∀ A : Set (Phase n), IsConvexDomain A → systolicRatio A ≤ ENNReal.ofReal C := by
  obtain ⟨c, hc⟩ := exists_goodCap hn
  set F : ℝ := ((2 * n).factorial : ℝ) with hFdef
  refine ⟨(2 * Real.pi) ^ n * F * (2 * (n : ℝ)) ^ (2 * n) / (n.factorial : ℝ), ?_⟩
  intro A hA
  obtain ⟨v, w, hw, hsub, hsup⟩ := exists_frame hn hA
  have hD := (volume_para_sq hw).2
  set D := (gram w).det with hDdef
  obtain ⟨a, b, hab⟩ := exists_det_le (d := 2 * n) (by omega) (gram w)⁻¹
  rw [Matrix.det_nonsing_inv, ← hDdef, Ring.inverse_eq_inv', abs_of_pos (inv_pos.2 hD)] at hab
  set g := (gram w)⁻¹ a b with hgdef
  have hg : g ≠ 0 := by
    intro h0
    rw [h0, abs_zero, zero_pow (by omega), mul_zero] at hab
    exact absurd hab (not_le.2 (inv_pos.2 hD))
  have hgpos : 0 < |g| := abs_pos.2 hg
  have hcap := cap_le_of_subset_para hn hc.1 hw hsub hg
  rw [hc.2 A hA] at hcap
  have hvol := vol_lower hn hA hw hsup
  set s := Real.sqrt D with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hD
  have hs2 : s ^ 2 = D := Real.sq_sqrt hD.le
  have hn0 : (0 : ℝ) < 2 * (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hY : 0 < (n.factorial : ℝ) * ((1 / (2 * (n : ℝ))) ^ (2 * n) * s) := by positivity
  unfold systolicRatio
  calc cEHZ A ^ n / ((n.factorial : ℝ≥0∞) * volume A)
      ≤ ENNReal.ofReal ((2 * Real.pi / |g|) ^ n) /
          ENNReal.ofReal ((n.factorial : ℝ) * ((1 / (2 * (n : ℝ))) ^ (2 * n) * s)) := by
        apply ENNReal.div_le_div
        · rw [ENNReal.ofReal_pow (by positivity)]
          exact ENNReal.pow_le_pow_left hcap
        · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
          gcongr
    _ = ENNReal.ofReal ((2 * Real.pi / |g|) ^ n /
          ((n.factorial : ℝ) * ((1 / (2 * (n : ℝ))) ^ (2 * n) * s))) :=
        (ENNReal.ofReal_div_of_pos hY).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_iff₀ hY]
        have hF : 1 ≤ F := by
          rw [hFdef]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
        have ht : 0 < |g| ^ n * s := by positivity
        have hkey : 1 ≤ F * (|g| ^ n * s) ^ 2 := by
          have : D⁻¹ ≤ F * |g| ^ (2 * n) := hab
          rw [mul_pow, ← pow_mul, mul_comm n 2, hs2]
          rw [inv_le_iff_one_le_mul₀ hD] at this
          nlinarith
        have h1 := real_ineq hF ht hkey
        have hnf : (0 : ℝ) < n.factorial := by positivity
        rw [div_pow, div_le_iff₀ (by positivity)]
        have e : (2 * Real.pi) ^ n * F * (2 * (n : ℝ)) ^ (2 * n) / (n.factorial : ℝ) *
            ((n.factorial : ℝ) * ((1 / (2 * (n : ℝ))) ^ (2 * n) * s)) * |g| ^ n =
            (2 * Real.pi) ^ n * (F * (|g| ^ n * s)) := by
          have hq : (1 / (2 * (n : ℝ))) ^ (2 * n) * (2 * (n : ℝ)) ^ (2 * n) = 1 := by
            rw [← mul_pow, one_div, inv_mul_cancel₀ hn0.ne', one_pow]
          have hnf' : (n.factorial : ℝ) ≠ 0 := hnf.ne'
          calc (2 * Real.pi) ^ n * F * (2 * (n : ℝ)) ^ (2 * n) / (n.factorial : ℝ) *
                ((n.factorial : ℝ) * ((1 / (2 * (n : ℝ))) ^ (2 * n) * s)) * |g| ^ n
              = (2 * Real.pi) ^ n * F * ((1 / (2 * (n : ℝ))) ^ (2 * n) *
                  (2 * (n : ℝ)) ^ (2 * n)) * (|g| ^ n * s) * ((n.factorial : ℝ) / n.factorial) := by
                ring
            _ = _ := by rw [hq, div_self hnf']; ring
        rw [e]
        have : (0 : ℝ) < (2 * Real.pi) ^ n := by positivity
        nlinarith

end Viterbo.MS.PartN
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part S1: `Sys` is bounded -/
alias systolicRatio_le_const := Viterbo.MS.PartN.systolicRatio_le_const

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartN
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part N: normal form of a body with `Sys ≥ δ` -/
theorem gram_smul (w : Fin (2 * n) → Phase n) (α : ℝ) :
    gram (fun i => α • w i) = (α ^ 2) • gram w := by
  ext i j
  simp only [gram, omega0, Matrix.of_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
    real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
  ring

theorem abs_entry_le_of_inv {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.det = 1) {β : ℝ}
    (hβ1 : 1 ≤ β) (hβ : ∀ a b, |M⁻¹ a b| ≤ β) (i j : Fin d) :
    |M i j| ≤ d.factorial * β ^ d := by
  have hu : IsUnit M.det := by rw [hM]; exact isUnit_one
  have hdet : M⁻¹.det = 1 := by
    rw [Matrix.det_nonsing_inv, hM]; simp
  have hMe : M = M⁻¹.adjugate := by
    conv_lhs => rw [← Matrix.nonsing_inv_nonsing_inv M hu]
    rw [Matrix.inv_def, hdet]; simp
  rw [hMe, Matrix.adjugate_apply]
  apply abs_det_le_of_entries
  intro a b
  rw [Matrix.updateRow_apply]
  split_ifs
  · rcases eq_or_ne i b with h | h
    · subst h; simp; exact hβ1
    · rw [Pi.single_eq_of_ne' h]; simp; linarith
  · exact hβ _ _

theorem normalize (hn : 1 ≤ n) {c : Set (Phase n) → ℝ≥0∞} (hc : GoodCap n c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, ∀ A : Set (Phase n), IsConvexDomain A → ENNReal.ofReal δ ≤ systolicRatio A →
      ∃ (A' : Set (Phase n)) (w : Fin (2 * n) → Phase n), IsConvexDomain A' ∧
        systolicRatio A' = systolicRatio A ∧ LinearIndependent ℝ w ∧
        A' ⊆ para 0 w (-1) 1 ∧ para 0 w 0 (1 / (2 * (n : ℝ))) ⊆ closure A' ∧
        (gram w).det = 1 ∧ ∀ a b, |gram w a b| ≤ B := by
  have hn0 : (0 : ℝ) < 2 * (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set η : ℝ := δ * (n.factorial : ℝ) * (1 / (2 * (n : ℝ))) ^ (2 * n) with hηdef
  have hη : 0 < η := by positivity
  set β : ℝ := max 1 ((2 * Real.pi) ^ n / η) with hβdef
  have hβ1 : 1 ≤ β := le_max_left _ _
  refine ⟨((2 * n).factorial : ℝ) * β ^ (2 * n), ?_⟩
  intro A hA hsysA
  obtain ⟨v, w, hw, hsub, hsup⟩ := exists_frame hn hA
  have hD := (volume_para_sq hw).2
  set D := (gram w).det with hDdef
  set s : ℝ := D ^ (-(1 / (2 * (n : ℝ)))) with hsdef
  have hs : 0 < s := Real.rpow_pos_of_pos hD _
  have hsD : s ^ (2 * n) * D = 1 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    have : -(1 / (2 * (n : ℝ))) * ((2 * n : ℕ) : ℝ) = -1 := by
      push_cast; field_simp
    rw [this, Real.rpow_neg_one, inv_mul_cancel₀ hD.ne']
  set α : ℝ := Real.sqrt s with hαdef
  have hα : 0 < α := Real.sqrt_pos.2 hs
  have hα2 : α ^ 2 = s := Real.sq_sqrt hs.le
  set w' : Fin (2 * n) → Phase n := fun i => α • w i with hw'def
  let Lα : Phase n ≃L[ℝ] Phase n :=
    (LinearEquiv.smulOfNeZero ℝ (Phase n) α hα.ne').toContinuousLinearEquiv
  have hLα : ∀ z, Lα z = α • z := fun z => rfl
  set A1 := (fun z => (ContinuousLinearEquiv.refl ℝ (Phase n)) z + (-v)) '' A with hA1def
  have hA1 : IsConvexDomain A1 := isConvexDomain_image_sympL _ _ hA
  have hsys1 : systolicRatio A1 = systolicRatio A :=
    sys_image_sympL hn hc _ (fun _ _ => rfl) _ hA
  set A' := α • A1 with hA'def
  have hA'img : A' = (fun z => α • (z + -v)) '' A := by
    rw [hA'def, hA1def, ← Set.image_smul, Set.image_image]; rfl
  have hA' : IsConvexDomain A' := by
    have h := isConvexDomain_image_sympL Lα 0 hA1
    have : (fun z => Lα z + 0) '' A1 = A' := by
      rw [hA'def, ← Set.image_smul]; congr 1; funext z; simp [hLα]
    rwa [this] at h
  have hsys' : systolicRatio A' = systolicRatio A := by
    rw [hA'def, sys_smul hn hc hA1 hα, hsys1]
  have hw' : LinearIndependent ℝ w' := by
    have e : w' = (Lα.toLinearEquiv : Phase n →ₗ[ℝ] Phase n) ∘ w := by funext i; rfl
    rw [e]
    exact hw.map' _ (LinearEquiv.ker _)
  have hgram : gram w' = s • gram w := by rw [hw'def, gram_smul, hα2]
  have hdet' : (gram w').det = 1 := by
    rw [hgram, Matrix.det_smul, Fintype.card_fin, ← hDdef, hsD]
  have hsub' : A' ⊆ para 0 w' (-1) 1 := by
    rw [hA'img]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hsub hx
    refine ⟨t, ht, ?_⟩
    simp only [hw'def, zero_add, add_neg_cancel_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]
  have hsup' : para 0 w' 0 (1 / (2 * (n : ℝ))) ⊆ closure A' := by
    rintro _ ⟨t, ht, rfl⟩
    have hx : v + ∑ i, t i • w i ∈ closure A := hsup ⟨t, ht, rfl⟩
    have hf : Continuous fun z : Phase n => α • (z + -v) := by fun_prop
    have := image_closure_subset_closure_image hf ⟨_, hx, rfl⟩
    rw [hA'img]
    convert this using 1
    simp only [hw'def, zero_add, add_neg_cancel_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]
  refine ⟨A', w', hA', hsys', hw', hsub', hsup', hdet', ?_⟩
  -- the bound on the inverse Gram matrix
  have hvol := vol_lower hn hA' hw' hsup'
  rw [hdet', Real.sqrt_one, mul_one] at hvol
  have hvtop : volume A' ≠ ⊤ := (vol_lt_top hA').ne
  have hv0 : volume A' ≠ 0 := by
    intro h0; rw [h0] at hvol
    exact absurd hvol (not_le.2 (ENNReal.ofReal_pos.2 (by positivity)))
  have hsysA' : ENNReal.ofReal δ ≤ systolicRatio A' := hsys' ▸ hsysA
  unfold systolicRatio at hsysA'
  rw [ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero (by simp [Nat.factorial_ne_zero]) hv0))
    (Or.inl (ENNReal.mul_ne_top (by simp) hvtop))] at hsysA'
  have hlow : ENNReal.ofReal η ≤ c A' ^ n := by
    rw [hc.2 A' hA']
    refine le_trans ?_ hsysA'
    rw [hηdef, mul_assoc, ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
    gcongr
  have hinv : ∀ a b, |(gram w')⁻¹ a b| ≤ β := by
    intro a b
    by_cases hg : (gram w')⁻¹ a b = 0
    · rw [hg, abs_zero]; linarith
    set g := (gram w')⁻¹ a b
    have hgpos : 0 < |g| := abs_pos.2 hg
    have hcap := cap_le_of_subset_para hn hc.1 hw' hsub' hg
    have h1 : ENNReal.ofReal η ≤ ENNReal.ofReal ((2 * Real.pi / |g|) ^ n) := by
      rw [ENNReal.ofReal_pow (by positivity)]
      exact hlow.trans (ENNReal.pow_le_pow_left hcap)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity), div_pow, le_div_iff₀ (by positivity)] at h1
    rcases le_or_gt |g| 1 with hg1 | hg1
    · linarith
    · have hgn : |g| ≤ |g| ^ n := le_self_pow₀ hg1.le (by omega)
      have : |g| ^ n ≤ (2 * Real.pi) ^ n / η := by
        rw [le_div_iff₀ hη]; linarith
      exact (hgn.trans this).trans (le_max_right _ _)
  intro a b
  exact abs_entry_le_of_inv _ hdet' hβ1 hinv a b

end Viterbo.MS.PartN
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part N: normal form of a body with `Sys ≥ δ` -/
alias normalize := Viterbo.MS.PartN.normalize

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartL
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
open Matrix
variable {n : ℕ}
noncomputable def bil {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) :
    (Fin m → Fin m → ℝ) →L[ℝ] (Fin m → Fin m → ℝ) →L[ℝ] (Fin m → Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        ((Fin m → Fin m → ℝ) →ₗ[ℝ] (Fin m → Fin m → ℝ)) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun X Y : Fin m → Fin m → ℝ =>
          Matrix.of.symm (Matrix.of X * P * Matrix.of Y))
        (fun X X' Y => by funext i j; simp [← Matrix.of_add_of, Matrix.add_mul])
        (fun c X Y => by funext i j; simp [← Matrix.smul_of])
        (fun X Y Y' => by funext i j; simp [← Matrix.of_add_of, Matrix.mul_add])
        (fun c X Y => by funext i j; simp [← Matrix.smul_of]))

theorem hasStrict {m : ℕ} (Q P : Fin m → Fin m → ℝ) :
    HasStrictFDerivAt (fun Y => Q + Y + (1/4 : ℝ) • bil P Y Y)
      ((ContinuousLinearEquiv.refl ℝ (Fin m → Fin m → ℝ) : (Fin m → Fin m → ℝ) →L[ℝ] _)) 0 := by
  have h1 := (bil P).hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id (0 : Fin m → Fin m → ℝ))
    (hasStrictFDerivAt_id (0 : Fin m → Fin m → ℝ))
  have h2 := ((hasStrictFDerivAt_id (0 : Fin m → Fin m → ℝ)).const_add Q).add (h1.const_smul (1/4 : ℝ))
  refine h2.congr_fderiv ?_
  ext Y i j
  simp

theorem inv_transpose_of_skew {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.det ≠ 0)
    (hQs : Qᵀ = -Q) : (Q⁻¹)ᵀ = -Q⁻¹ := by
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ
  rw [Matrix.transpose_nonsing_inv, hQs]
  apply Matrix.inv_eq_left_inv
  rw [neg_mul_neg, Matrix.nonsing_inv_mul _ hu]

theorem exists_S {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.det ≠ 0) (hQs : Qᵀ = -Q)
    {Qk : ℕ → Matrix (Fin m) (Fin m) ℝ} (hk : Tendsto Qk atTop (𝓝 Q))
    (hks : ∀ k, (Qk k)ᵀ = -Qk k) :
    ∃ S : ℕ → Matrix (Fin m) (Fin m) ℝ, Tendsto S atTop (𝓝 1) ∧
      ∀ᶠ k in atTop, (S k)ᵀ * Q * S k = Qk k := by
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ
  set P : Matrix (Fin m) (Fin m) ℝ := Q⁻¹ with hP
  have hPt : Pᵀ = -P := inv_transpose_of_skew hQ hQs
  have hPQ : ∀ X : Matrix (Fin m) (Fin m) ℝ, P * (Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hP, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hQP : ∀ X : Matrix (Fin m) (Fin m) ℝ, Q * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hP, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have hPQ1 : P * Q = 1 := Matrix.nonsing_inv_mul _ hu
  set G : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun Y => Q + Y + (1/4 : ℝ) • (Y * P * Y) with hG
  have hGm : ∀ Y : Matrix (Fin m) (Fin m) ℝ, G Y = Q + Y + (1/4 : ℝ) • (Y * P * Y) :=
    fun Y => rfl
  have hf : HasStrictFDerivAt (𝕜 := ℝ) (E := Fin m → Fin m → ℝ) (F := Fin m → Fin m → ℝ) G
      ((ContinuousLinearEquiv.refl ℝ (Fin m → Fin m → ℝ) : (Fin m → Fin m → ℝ) →L[ℝ] _)) 0 :=
    hasStrict (m := m) Q P
  have hG0 : G 0 = Q := by simp [hG]
  set g := HasStrictFDerivAt.localInverse (𝕜 := ℝ) (E := Fin m → Fin m → ℝ)
    (F := Fin m → Fin m → ℝ) G (ContinuousLinearEquiv.refl ℝ _) 0 hf with hg
  have hk' : Tendsto Qk atTop (𝓝 (G 0)) := by rw [hG0]; exact hk
  set Y : ℕ → Matrix (Fin m) (Fin m) ℝ := fun k => g (Qk k) with hYdef
  have hY : Tendsto Y atTop (𝓝 0) := hf.localInverse_tendsto.comp hk'
  have hGY : ∀ᶠ k in atTop, G (Y k) = Qk k := hk'.eventually hf.eventually_right_inverse
  -- skewness
  have hZ : Tendsto (fun k => -(Y k)ᵀ) atTop (𝓝 0) := by
    have := ((continuous_id.matrix_transpose).neg.tendsto (0 : Matrix (Fin m) (Fin m) ℝ)).comp hY
    simpa [Function.comp_def] using this
  have hL1 : ∀ᶠ k in atTop, g (G (Y k)) = Y k := hY.eventually hf.eventually_left_inverse
  have hL2 : ∀ᶠ k in atTop, g (G (-(Y k)ᵀ)) = -(Y k)ᵀ := hZ.eventually hf.eventually_left_inverse
  have hskew : ∀ Y : Matrix (Fin m) (Fin m) ℝ, G (-Yᵀ) = -(G Y : Matrix (Fin m) (Fin m) ℝ)ᵀ := by
    intro Y
    rw [hGm, hGm]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, hQs, hPt,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_add, smul_neg, Matrix.mul_assoc]
  have hYs : ∀ᶠ k in atTop, (Y k)ᵀ = -Y k := by
    filter_upwards [hGY, hL1, hL2] with k h1 h2 h3
    have h4 : G (-(Y k)ᵀ) = Qk k := by rw [hskew, h1, hks, neg_neg]
    rw [h4, ← h1, h2] at h3
    nth_rw 2 [h3]
    rw [neg_neg]
  refine ⟨fun k => 1 + (1/2 : ℝ) • (P * Y k), ?_, ?_⟩
  · have := ((tendsto_const_nhds (x := P)).mul hY).const_smul (1/2 : ℝ) |>.const_add
      (1 : Matrix (Fin m) (Fin m) ℝ)
    simpa using this
  · filter_upwards [hGY, hYs] with k h1 h2
    rw [← h1, hGm]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_one,
      h2, hPt, neg_mul_neg, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hQP]
    rw [hPQ1, Matrix.mul_one]
    module

/-! ## The symplectic form as a bilinear map -/
set_option linter.unusedSimpArgs false in
noncomputable def omegaB (n : ℕ) : Phase n →ₗ[ℝ] Phase n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => omega0 v w)
    (fun v v' w => by simp [omega0, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]; ring)
    (fun c v w => by simp [omega0, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]; ring)
    (fun v w w' => by simp [omega0, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]; ring)
    (fun c v w => by simp [omega0, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]; ring)

theorem omegaB_apply {n : ℕ} (v w : Phase n) : omegaB n v w = omega0 v w := rfl

theorem gram_transpose {n : ℕ} (v : Fin (2 * n) → Phase n) : (gram v)ᵀ = -gram v := by
  ext i j
  simp only [gram, Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply, omega0]
  ring

theorem gram_comb {n : ℕ} (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (u : Fin (2 * n) → Phase n) :
    gram (fun j => ∑ i, M i j • u i) = Mᵀ * gram u * M := by
  ext a b
  simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [← omegaB_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    omegaB_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem linIndep_of_gram {n : ℕ} {v : Fin (2 * n) → Phase n} (h : (gram v).det ≠ 0) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hm : (gram v).mulVec g = 0 := by
    funext i
    have : omegaB n (v i) (∑ j, g j • v j) = 0 := by rw [hg, map_zero]
    simp only [map_sum, map_smul, smul_eq_mul, omegaB_apply] at this
    simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := Matrix.eq_zero_of_mulVec_eq_zero h hm
  intro i
  rw [this, Pi.zero_apply]

theorem finrank_phase (n : ℕ) : Module.finrank ℝ (Phase n) = 2 * n := by
  simp [Module.finrank_prod]
  omega

theorem sympl_of_gram {n : ℕ} (hn : 1 ≤ n) {v t : Fin (2 * n) → Phase n} (hv : LinearIndependent ℝ v)
    (ht : LinearIndependent ℝ t) (h : gram v = gram t) :
    ∃ L : Phase n ≃L[ℝ] Phase n, IsSympL L ∧ ∀ i, L (v i) = t i := by
  have hcard : Fintype.card (Fin (2 * n)) = Module.finrank ℝ (Phase n) := by
    rw [finrank_phase, Fintype.card_fin]
  have : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  set bv := basisOfLinearIndependentOfCardEqFinrank hv hcard with hbv
  set bt := basisOfLinearIndependentOfCardEqFinrank ht hcard with hbt
  set Le := bv.equiv bt (Equiv.refl _) with hLe_def
  have hLe : ∀ i, Le (v i) = t i := by
    intro i
    have := bv.equiv_apply i bt (Equiv.refl _)
    simpa [bv, bt] using this
  refine ⟨Le.toContinuousLinearEquiv, ?_, fun i => hLe i⟩
  have hB : (omegaB n).compl₁₂ Le.toLinearMap Le.toLinearMap = omegaB n := by
    refine LinearMap.ext_basis bv bv fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, hbv,
      coe_basisOfLinearIndependentOfCardEqFinrank, hLe, omegaB_apply]
    have := congrFun (congrFun h i) j
    simpa [gram] using this.symm
  intro x y
  have := congrArg (fun B : Phase n →ₗ[ℝ] Phase n →ₗ[ℝ] ℝ => B x y) hB
  simpa [omegaB_apply] using this

/-! ## Part L -/
theorem exists_sympL_tendsto (hn : 1 ≤ n) {w : ℕ → Fin (2 * n) → Phase n}
    (hw : ∀ k, LinearIndependent ℝ (w k)) {Q : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ}
    (hQ : Tendsto (fun k => gram (w k)) atTop (𝓝 Q)) (hQdet : Q.det ≠ 0) :
    ∃ (L : ℕ → Phase n ≃L[ℝ] Phase n) (u : Fin (2 * n) → Phase n), (∀ k, IsSympL (L k)) ∧
      LinearIndependent ℝ u ∧ Tendsto (fun k i => L k (w k i)) atTop (𝓝 u) := by
  have hks : ∀ k, (gram (w k))ᵀ = -gram (w k) := fun k => gram_transpose _
  have hQs : Qᵀ = -Q := by
    have h1 : Tendsto (fun k => (gram (w k))ᵀ) atTop (𝓝 Qᵀ) :=
      (continuous_id.matrix_transpose.tendsto Q).comp hQ
    have h2 : Tendsto (fun k => (gram (w k))ᵀ) atTop (𝓝 (-Q)) := by
      simp_rw [hks]; exact hQ.neg
    exact tendsto_nhds_unique h1 h2
  obtain ⟨S, hS1, hSeq⟩ := exists_S hQdet hQs hQ hks
  have hdet : ∀ᶠ k in atTop, (gram (w k)).det ≠ 0 :=
    (((continuous_id.matrix_det).tendsto Q).comp hQ).eventually (eventually_ne_nhds hQdet)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hSeq.and hdet)
  set S0 := S k₀ with hS0
  have hS0det : S0.det ≠ 0 := by
    intro h0
    apply (hk₀ k₀ le_rfl).2
    rw [← (hk₀ k₀ le_rfl).1, Matrix.det_mul, h0, mul_zero]
  have hu0 : IsUnit S0.det := isUnit_iff_ne_zero.mpr hS0det
  set u : Fin (2 * n) → Phase n := fun j => ∑ i, (S0⁻¹) i j • w k₀ i with hudef
  have hgu : gram u = Q := by
    rw [hudef, gram_comb, ← (hk₀ k₀ le_rfl).1]
    calc (S0⁻¹)ᵀ * (S0ᵀ * Q * S0) * S0⁻¹ = ((S0⁻¹)ᵀ * S0ᵀ) * Q * (S0 * S0⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Q := by
          rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu0, Matrix.transpose_one,
            Matrix.one_mul, Matrix.mul_one]
  set t : ℕ → Fin (2 * n) → Phase n := fun k j => ∑ i, S k i j • u i with htdef
  have hgt : ∀ k, k₀ ≤ k → gram (t k) = gram (w k) := by
    intro k hk
    rw [htdef, gram_comb, hgu]
    exact (hk₀ k hk).1
  have hL : ∀ k, ∃ L : Phase n ≃L[ℝ] Phase n, IsSympL L ∧ (k₀ ≤ k → ∀ i, L (w k i) = t k i) := by
    intro k
    by_cases hk : k₀ ≤ k
    · obtain ⟨L, hL1, hL2⟩ := sympl_of_gram hn (hw k)
        (linIndep_of_gram (by rw [hgt k hk]; exact (hk₀ k hk).2)) (hgt k hk).symm
      exact ⟨L, hL1, fun _ => hL2⟩
    · exact ⟨ContinuousLinearEquiv.refl ℝ _, fun _ _ => rfl, fun h => absurd h hk⟩
  choose L hLs hLt using hL
  refine ⟨L, u, hLs, linIndep_of_gram (by rw [hgu]; exact hQdet), ?_⟩
  have hc : Continuous (fun M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ =>
      fun j => ∑ i, M i j • u i) := by
    fun_prop
  have ht : Tendsto t atTop (𝓝 u) := by
    have := (hc.tendsto 1).comp hS1
    have h1 : (fun j => ∑ i, (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) i j • u i) = u := by
      funext j
      simp [Matrix.one_apply]
    rw [h1] at this
    exact this
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop k₀] with k hk
  funext i
  exact (hLt k hk i).symm

end Viterbo.MS.PartL
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part L: symplectic maps making frames converge -/
alias exists_sympL_tendsto := Viterbo.MS.PartL.exists_sympL_tendsto

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartB
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem finrank_phase : Module.finrank ℝ (Phase n) = 2 * n := by
  rw [Module.finrank_prod, finrank_euclideanSpace_fin]; ring

/-- A parallelotope on a linearly independent frame with `δ > 0` has nonempty interior. -/
theorem interior_para_nonempty {w : Fin (2 * n) → Phase n} (hw : LinearIndependent ℝ w)
    {δ : ℝ} (hδ : 0 < δ) : (interior (para 0 w 0 δ)).Nonempty := by
  let b := basisOfLinearIndependentOfCardEqFinrank' w hw (by rw [Fintype.card_fin, finrank_phase])
  let T : (Fin (2 * n) → ℝ) ≃L[ℝ] Phase n := b.equivFun.symm.toContinuousLinearEquiv
  have hT : ∀ t, T t = ∑ i, t i • w i := fun t => by
    simp [T, b, Module.Basis.equivFun_symm_apply]
  have hO : IsOpen (T '' (Set.pi univ fun _ => Ioo 0 δ)) :=
    T.isOpenMap _ (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)
  have hsub : T '' (Set.pi univ fun _ => Ioo 0 δ) ⊆ para 0 w 0 δ := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨t, fun i => Ioo_subset_Icc_self (ht i (mem_univ _)), ?_⟩
    rw [hT, zero_add]
  refine ⟨T fun _ => δ / 2, interior_maximal hsub hO ⟨_, fun i _ => ⟨by linarith, by linarith⟩, rfl⟩⟩

theorem blaschke {K : ℕ → Set (Phase n)} {u : ℕ → Fin (2 * n) → Phase n}
    {uLim : Fin (2 * n) → Phase n} {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ k, IsCompact (K k) ∧ Convex ℝ (K k)) (hsub : ∀ k, K k ⊆ para 0 (u k) (-1) 1)
    (hsup : ∀ k, para 0 (u k) 0 δ ⊆ K k) (hu : Tendsto u atTop (𝓝 uLim))
    (huLim : LinearIndependent ℝ uLim) :
    ∃ (φ : ℕ → ℕ) (KLim : Set (Phase n)), StrictMono φ ∧ IsCompact KLim ∧ Convex ℝ KLim ∧
      (interior KLim).Nonempty ∧ Tendsto (fun k => Metric.hausdorffDist (K (φ k)) KLim) atTop (𝓝 0) := by
  classical
  -- a uniform bound on the frames
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ k i, ‖u k i‖ ≤ R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto u hu).subset_closedBall 0
    refine ⟨R, fun k i => (norm_le_pi_norm (u k) i).trans ?_⟩
    simpa using hR ⟨k, rfl⟩
  set ρ : ℝ := ∑ _i : Fin (2 * n), R
  have hKball : ∀ k, K k ⊆ Metric.closedBall 0 ρ := by
    intro k z hz
    obtain ⟨t, ht, rfl⟩ := hsub k hz
    rw [mem_closedBall_zero_iff, zero_add]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have : |t i| ≤ 1 := abs_le.2 (ht i)
    calc |t i| * ‖u k i‖ ≤ 1 * ‖u k i‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ ≤ R := by rw [one_mul]; exact hR k i
  have h0 : ∀ k, (0 : Phase n) ∈ K k := fun k =>
    hsup k ⟨0, fun _ => ⟨le_rfl, hδ.le⟩, by simp⟩
  let S := Metric.closedBall (0 : Phase n) ρ
  have : CompactSpace S := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  have hemb : Topology.IsClosedEmbedding (Subtype.val : S → Phase n) :=
    Metric.isClosed_closedBall.isClosedEmbedding_subtypeVal
  have hcomp : ∀ k, IsCompact ((Subtype.val : S → Phase n) ⁻¹' K k) := fun k =>
    hemb.isCompact_preimage (hK k).1
  let F : ℕ → TopologicalSpace.NonemptyCompacts S := fun k =>
    ⟨⟨_, hcomp k⟩, ⟨⟨0, hKball k (h0 k)⟩, h0 k⟩⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_univ (X := TopologicalSpace.NonemptyCompacts S)).tendsto_subseq
      (x := F) (fun _ => mem_univ _)
  set KLim : Set (Phase n) := Subtype.val '' (a : Set S) with hKLimdef
  have himg : ∀ k, Subtype.val '' ((F k : Set S)) = K k := fun k => by
    change Subtype.val '' ((Subtype.val : S → Phase n) ⁻¹' K k) = K k
    rw [Subtype.image_preimage_coe, inter_eq_right.2 (hKball k)]
  have hKLimc : IsCompact KLim := a.isCompact.image continuous_subtype_val
  have hKLimne : KLim.Nonempty := a.nonempty.image _
  have htend : Tendsto (fun k => Metric.hausdorffDist (K (φ k)) KLim) atTop (𝓝 0) := by
    have := (tendsto_iff_dist_tendsto_zero.1 hlim)
    refine this.congr fun k => ?_
    rw [Metric.NonemptyCompacts.dist_eq, ← Metric.hausdorffDist_image isometry_subtype_coe,
      Function.comp_apply, himg]
  have hfin : ∀ k, Metric.hausdorffEDist (K (φ k)) KLim ≠ ⊤ := fun k =>
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨0, h0 _⟩ hKLimne
      (hK _).1.isBounded hKLimc.isBounded
  -- limits of points of `K (φ k)` lie in `KLim`
  have hmem : ∀ (z : Phase n) (zs : ℕ → Phase n), (∀ k, zs k ∈ K (φ k)) →
      Tendsto zs atTop (𝓝 z) → z ∈ KLim := by
    intro z zs hzs hz
    rw [hKLimc.isClosed.mem_iff_infDist_zero hKLimne]
    refine le_antisymm ?_ Metric.infDist_nonneg
    have h1 : Tendsto (fun k => dist (zs k) z + Metric.hausdorffDist (K (φ k)) KLim) atTop
        (𝓝 (0 + 0)) := (tendsto_iff_dist_tendsto_zero.1 hz).add htend
    rw [add_zero] at h1
    refine ge_of_tendsto' h1 fun k => ?_
    calc Metric.infDist z KLim ≤ Metric.infDist (zs k) KLim + dist z (zs k) :=
          Metric.infDist_le_infDist_add_dist
      _ ≤ Metric.hausdorffDist (K (φ k)) KLim + dist z (zs k) := by
          gcongr; exact Metric.infDist_le_hausdorffDist_of_mem (hzs k) (hfin k)
      _ = _ := by rw [dist_comm]; ring
  -- points of `KLim` are limits of points of `K (φ k)`
  have happrox : ∀ x ∈ KLim, ∃ xs : ℕ → Phase n, (∀ k, xs k ∈ K (φ k)) ∧
      Tendsto xs atTop (𝓝 x) := by
    intro x hx
    have : ∀ k, ∃ y ∈ K (φ k), dist y x <
        Metric.hausdorffDist (K (φ k)) KLim + 1 / ((k : ℝ) + 1) := fun k =>
      Metric.exists_dist_lt_of_hausdorffDist_lt' hx
        (lt_add_of_pos_right _ Nat.one_div_pos_of_nat) (hfin k)
    choose xs hxs hd using this
    refine ⟨xs, hxs, tendsto_iff_dist_tendsto_zero.2 ?_⟩
    have h2 := htend.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h2
    exact squeeze_zero (fun _ => dist_nonneg) (fun k => (hd k).le) h2
  refine ⟨φ, KLim, hφ, hKLimc, ?_, ?_, htend⟩
  · intro x hx y hy p q hp hq hpq
    obtain ⟨xs, hxs, hxl⟩ := happrox x hx
    obtain ⟨ys, hys, hyl⟩ := happrox y hy
    exact hmem _ (fun k => p • xs k + q • ys k) (fun k => (hK _).2 (hxs k) (hys k) hp hq hpq)
      ((hxl.const_smul p).add (hyl.const_smul q))
  · have hpara : para 0 uLim 0 δ ⊆ KLim := by
      rintro z ⟨t, ht, rfl⟩
      have hu' : Tendsto (fun k => u (φ k)) atTop (𝓝 uLim) := hu.comp hφ.tendsto_atTop
      refine hmem _ (fun k => ∑ i, t i • u (φ k) i)
        (fun k => hsup _ ⟨t, ht, by rw [zero_add]⟩) ?_
      rw [zero_add]
      exact tendsto_finsetSum _ fun i _ => (tendsto_pi_nhds.1 hu' i).const_smul (t i)
    exact (interior_para_nonempty huLim hδ).mono (interior_mono hpara)

end Viterbo.MS.PartB
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part B: Blaschke selection and the homothety sandwich -/
alias blaschke := Viterbo.MS.PartB.blaschke

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartB
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem sandwich {K : ℕ → Set (Phase n)} {KLim : Set (Phase n)}
    (hK : ∀ k, IsCompact (K k) ∧ Convex ℝ (K k) ∧ (K k).Nonempty) (hKLim : IsCompact KLim)
    (hKLimc : Convex ℝ KLim) {p : Phase n} (hp : p ∈ interior KLim)
    (hlim : Tendsto (fun k => Metric.hausdorffDist (K k) KLim) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) :
    ∀ᶠ k in atTop, (fun z => p + (1 - ε) • (z - p)) '' KLim ⊆ K k ∧
      K k ⊆ (fun z => p + (1 + ε) • (z - p)) '' KLim := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hp)
  have hKLimne : KLim.Nonempty := ⟨p, interior_subset hp⟩
  have hev : ∀ᶠ k in atTop, Metric.hausdorffDist (K k) KLim < ε * r / 2 :=
    (tendsto_order.1 hlim).2 _ (by positivity)
  filter_upwards [hev] with k hk
  have hfin : Metric.hausdorffEDist (K k) KLim ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hK k).2.2 hKLimne
      (hK k).1.isBounded hKLim.isBounded
  have hk' : Metric.hausdorffDist (K k) KLim < ε * r := by
    have : 0 < ε * r := by positivity
    linarith
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    by_contra hy
    obtain ⟨f, c, hfK, hfy⟩ :=
      geometric_hahn_banach_closed_point (hK k).2.1 (hK k).1.isClosed hy
    obtain ⟨z0, hz0⟩ := (hK k).2.2
    have hfpos : 0 < ‖f‖ := by
      rw [norm_pos_iff]
      rintro rfl
      have := hfK z0 hz0
      simp at this hfy
      linarith
    obtain ⟨e, he1, hfe⟩ : ∃ e : Phase n, ‖e‖ < 1 ∧ ‖f‖ / 2 < f e := by
      obtain ⟨e, he1, hfe⟩ := f.exists_lt_apply_of_lt_opNorm (r := ‖f‖ / 2) (by linarith)
      rw [Real.norm_eq_abs] at hfe
      rcases le_or_gt 0 (f e) with h | h
      · exact ⟨e, he1, by rwa [abs_of_nonneg h] at hfe⟩
      · refine ⟨-e, by rwa [norm_neg], ?_⟩
        rw [map_neg]; rwa [abs_of_neg h] at hfe
    set y := p + (1 - ε) • (x - p)
    set w := y + (ε * r) • e
    have hq : p + r • e ∈ KLim := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr]
      calc r * ‖e‖ < r * 1 := by gcongr
        _ = r := mul_one r
    have hw : w ∈ KLim := by
      have hw' : w = (1 - ε) • x + ε • (p + r • e) := by
        simp only [w, y]; module
      rw [hw']
      exact hKLimc hx hq (by linarith) hε.le (by ring)
    obtain ⟨z, hz, hdz⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hw hk hfin
    have h1 : f w - f z ≤ ‖f‖ * ‖w - z‖ := by
      rw [← map_sub]; exact (le_abs_self _).trans (f.le_opNorm _)
    have h2 : ‖w - z‖ < ε * r / 2 := by rwa [← dist_eq_norm, dist_comm]
    have h3 : f w = f y + (ε * r) * f e := by simp [w, map_add, map_smul]
    have h4 := hfK z hz
    have h5 : ‖f‖ * ‖w - z‖ ≤ ‖f‖ * (ε * r / 2) := by gcongr
    have h6 : (ε * r) * (‖f‖ / 2) < (ε * r) * f e := by
      have : 0 < ε * r := by positivity
      gcongr
    nlinarith
  · intro z hz
    obtain ⟨y, hy, hdy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hz hk' hfin
    have hε1' : (0 : ℝ) < 1 + ε := by linarith
    set q := p + ε⁻¹ • (z - y)
    have hq : q ∈ KLim := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hε), ← dist_eq_norm, inv_mul_lt_iff₀ hε]
      exact hdy
    refine ⟨p + (1 + ε)⁻¹ • (z - p), ?_, ?_⟩
    · have hx : p + (1 + ε)⁻¹ • (z - p) = (1 / (1 + ε)) • y + (ε / (1 + ε)) • q := by
        simp only [q]
        match_scalars <;> field_simp <;> ring
      rw [hx]
      refine hKLimc hy hq (by positivity) (by positivity) ?_
      field_simp
    · simp only [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hε1'.ne', one_smul,
        add_sub_cancel]

end Viterbo.MS.PartB
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
alias sandwich := Viterbo.MS.PartB.sandwich

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartS2
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem para_eq_image (v : Phase n) (w : Fin (2 * n) → Phase n) (a b : ℝ) :
    para v w a b = (fun t : Fin (2 * n) → ℝ => v + ∑ i, t i • w i) '' (Set.pi univ fun _ => Icc a b) := by
  ext z
  simp only [para, Set.mem_ofPred_eq, mem_image, Set.mem_univ_pi]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩

theorem isClosed_para (v : Phase n) (w : Fin (2 * n) → Phase n) (a b : ℝ) :
    IsClosed (para v w a b) := by
  rw [para_eq_image]
  refine ((isCompact_univ_pi fun _ => isCompact_Icc).image ?_).isClosed
  fun_prop

theorem image_para (L : Phase n ≃L[ℝ] Phase n) (w : Fin (2 * n) → Phase n) (a b : ℝ) :
    (fun z => L z + 0) '' para 0 w a b = para 0 (fun i => L (w i)) a b := by
  ext z
  simp only [para, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, by simp [map_sum, map_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, ⟨t, ht, rfl⟩, by simp [map_sum, map_smul]⟩

theorem attained (hn : 1 ≤ n) (hfin : maxSystolicRatio n < ⊤) :
    ∃ A : Set (Phase n), IsConvexDomain A ∧ systolicRatio A = maxSystolicRatio n := by
  set S := maxSystolicRatio n with hS
  have hle : ∀ A : Set (Phase n), IsConvexDomain A → systolicRatio A ≤ S := fun A hA =>
    le_iSup₂ (f := fun (A : Set (Phase n)) (_ : IsConvexDomain A) => systolicRatio A) A hA
  rcases eq_or_ne S 0 with h0 | h0
  · refine ⟨Metric.ball 0 1, ⟨Metric.isBounded_ball, convex_ball _ _, ?_⟩, ?_⟩
    · rw [Metric.isOpen_ball.interior_eq]; exact ⟨0, Metric.mem_ball_self one_pos⟩
    · refine le_antisymm ?_ (by rw [h0]; simp)
      exact hle _ ⟨Metric.isBounded_ball, convex_ball _ _, by
        rw [Metric.isOpen_ball.interior_eq]; exact ⟨0, Metric.mem_ball_self one_pos⟩⟩
  obtain ⟨c, hc⟩ := exists_goodCap hn
  have hStop : S ≠ ⊤ := hfin.ne
  have hSpos : 0 < S.toReal := ENNReal.toReal_pos h0 hStop
  set δ : ℝ := S.toReal / 2 with hδdef
  have hδ : 0 < δ := by positivity
  -- the approximating values
  set r : ℕ → ℝ := fun k => S.toReal * (1 - (1 / ((k : ℝ) + 1)) / 2) with hrdef
  have hr_lt : ∀ k, r k < S.toReal := by
    intro k
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    simp only [hrdef]; nlinarith
  have hr_ge : ∀ k, δ ≤ r k := by
    intro k
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    simp only [hrdef, hδdef]; nlinarith
  have hr_tend : Tendsto r atTop (𝓝 S.toReal) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := (tendsto_const_nhds (x := S.toReal)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (h.div_const 2))
    show Tendsto (fun k : ℕ => S.toReal * (1 - (1 / ((k : ℝ) + 1)) / 2)) atTop (𝓝 S.toReal)
    simpa using this
  have hA : ∀ k, ∃ A : Set (Phase n), IsConvexDomain A ∧ ENNReal.ofReal (r k) < systolicRatio A := by
    intro k
    have : ENNReal.ofReal (r k) < S :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [hr_ge k]) hStop).2 (hr_lt k)
    rw [hS, maxSystolicRatio] at this
    obtain ⟨A, hA⟩ := lt_iSup_iff.1 this
    obtain ⟨hAc, hA⟩ := lt_iSup_iff.1 hA
    exact ⟨A, hAc, hA⟩
  choose A hAc hAr using hA
  obtain ⟨B, hB⟩ := normalize hn hc hδ
  have hN := fun k => hB (A k) (hAc k)
    (le_trans (ENNReal.ofReal_le_ofReal (hr_ge k)) (hAr k).le)
  choose A' w hA'c hA's hw hA'sub hA'sup hwdet hwB using hN
  -- a convergent subsequence of Gram matrices
  obtain ⟨Q, -, ψ, hψ, hQ⟩ := (isCompact_univ_pi fun _ : Fin (2 * n) =>
      isCompact_univ_pi fun _ : Fin (2 * n) => isCompact_Icc (a := -B) (b := B)).tendsto_subseq
      (x := fun k (i j : Fin (2 * n)) => gram (w k) i j)
      (fun k => by
        simp only [Set.mem_univ_pi, mem_Icc]
        intro i j; exact abs_le.1 (hwB k i j))
  have hQ' : Tendsto (fun k => gram (w (ψ k))) atTop (𝓝 (Matrix.of Q)) :=
    hQ
  have hQdet : (Matrix.of Q).det = 1 := by
    have h1 := ((continuous_id.matrix_det :
      Continuous fun M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ => M.det).tendsto _).comp hQ'
    have h2 : Tendsto (fun k => (gram (w (ψ k))).det) atTop (𝓝 1) := by
      simp only [hwdet]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  obtain ⟨L, u, hL, hu, hLu⟩ := exists_sympL_tendsto hn (w := fun k => w (ψ k)) (fun k => hw _) hQ'
    (by rw [hQdet]; exact one_ne_zero)
  -- the bodies
  set D : ℕ → Set (Phase n) := fun k => (fun z => L k z + 0) '' A' (ψ k) with hDdef
  set K : ℕ → Set (Phase n) := fun k => closure (D k) with hKdef
  have hDc : ∀ k, IsConvexDomain (D k) := fun k => isConvexDomain_image_sympL (L k) 0 (hA'c _)
  have hKc : ∀ k, IsConvexDomain (K k) := fun k => isConvexDomain_closure (hDc k)
  have hKcpt : ∀ k, IsCompact (K k) := fun k =>
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hDc k).1.closure
  have hKsys : ∀ k, systolicRatio (K k) = systolicRatio (A (ψ k)) := by
    intro k
    rw [hKdef, sys_closure hn hc (hDc k), hDdef, sys_image_sympL hn hc (L k) (hL k) 0 (hA'c _),
      hA's]
  have hn' : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hcont : ∀ k, Continuous (fun z => L k z + 0) := fun k => by fun_prop
  obtain ⟨φ, KLim, hφ, hKLc, hKLcv, hKLi, hhaus⟩ :=
    blaschke (K := K) (u := fun k i => L k (w (ψ k) i)) (uLim := u) hn'
      (fun k => ⟨hKcpt k, (hKc k).2.1⟩)
      (fun k => by
        refine closure_minimal ?_ (isClosed_para _ _ _ _)
        rw [← image_para]
        exact image_mono (hA'sub _))
      (fun k => by
        rw [← image_para]
        exact (image_mono (hA'sup _)).trans (image_closure_subset_closure_image (hcont k)))
      hLu hu
  have hKL : IsConvexDomain KLim := ⟨hKLc.isBounded, hKLcv, hKLi⟩
  obtain ⟨p, hp⟩ := hKLi
  set s := (systolicRatio KLim).toReal with hsdef
  have hsys_ne : systolicRatio KLim ≠ ⊤ := ne_top_of_le_ne_top hStop (hle _ hKL)
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  -- for each ε, `S ≤ ((1+ε)/(1-ε))^(2n) * s`
  have hmain : ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → S.toReal ≤ ((1 + ε) / (1 - ε)) ^ (2 * n) * s := by
    rintro ε ⟨hε0, hε1⟩
    have hev := sandwich (K := fun k => K (φ k)) (KLim := KLim)
      (fun k => ⟨hKcpt _, (hKc _).2.1, (hKc _).2.2.mono interior_subset⟩)
      hKLc hKLcv hp hhaus hε0 hε1
    have hf0 : 0 ≤ ((1 + ε) / (1 - ε)) ^ (2 * n) := by
      apply pow_nonneg; apply div_nonneg <;> linarith
    refine le_of_tendsto (hr_tend.comp ((hψ.comp hφ).tendsto_atTop)) ?_
    filter_upwards [hev] with k hk
    have h1 := sys_le_of_sandwich hn hc (hKc (φ k)) hKL hε0 hε1 hk.1 hk.2
    rw [hKsys] at h1
    have h2 := (hAr (ψ (φ k))).le.trans h1
    rw [← ENNReal.ofReal_toReal hsys_ne, ← ENNReal.ofReal_mul hf0] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hf0 hs0)).1 h2
  have hcontε : ContinuousAt (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ (2 * n) * s) 0 := by
    apply ContinuousAt.mul _ continuousAt_const
    apply ContinuousAt.pow
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  have hlim : Tendsto (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ (2 * n) * s) (𝓝[>] 0) (𝓝 s) := by
    have := hcontε.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hSs : S.toReal ≤ s :=
    ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun ε hε => hmain ε hε)
  refine ⟨KLim, hKL, le_antisymm (hle _ hKL) ?_⟩
  rw [← ENNReal.ofReal_toReal hStop, ← ENNReal.ofReal_toReal hsys_ne]
  exact ENNReal.ofReal_le_ofReal hSs

end Viterbo.MS.PartS2
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part S2: the supremum is attained -/
alias attained := Viterbo.MS.PartS2.attained

end Viterbo.MS
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartM
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {m k : ℕ}
/-! Helpers copied from `Solutions/Viterbo/PP2PartG.lean`. -/
/-- First block of coordinates. -/
noncomputable def P1L : Position (m + k) →ₗ[ℝ] Position m where
  toFun x := WithLp.toLp 2 (fun i => x (Fin.castAdd k i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- Second block of coordinates. -/
noncomputable def P2L : Position (m + k) →ₗ[ℝ] Position k where
  toFun x := WithLp.toLp 2 (fun i => x (Fin.natAdd m i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

noncomputable def P1 : Position (m + k) →L[ℝ] Position m := LinearMap.toContinuousLinearMap P1L

noncomputable def P2 : Position (m + k) →L[ℝ] Position k := LinearMap.toContinuousLinearMap P2L

lemma P1_apply (x : Position (m + k)) (i : Fin m) : (P1 x) i = x (Fin.castAdd k i) := rfl

lemma P2_apply (x : Position (m + k)) (i : Fin k) : (P2 x) i = x (Fin.natAdd m i) := rfl

lemma appendPos_castAdd (x : Position m) (y : Position k) (i : Fin m) :
    appendPos x y (Fin.castAdd k i) = x i := by
  simp [appendPos]

lemma appendPos_natAdd (x : Position m) (y : Position k) (i : Fin k) :
    appendPos x y (Fin.natAdd m i) = y i := by
  simp [appendPos]

lemma P1_append (x : Position m) (y : Position k) : P1 (appendPos x y) = x := by
  ext i; rw [P1_apply, appendPos_castAdd]

lemma P2_append (x : Position m) (y : Position k) : P2 (appendPos x y) = y := by
  ext i; rw [P2_apply, appendPos_natAdd]

lemma append_P (x : Position (m + k)) : appendPos (P1 x) (P2 x) = x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [appendPos_castAdd, P1_apply]
  · rw [appendPos_natAdd, P2_apply]

/-- First phase block. -/
noncomputable def Q1 : Phase (m + k) →L[ℝ] Phase m :=
  (P1.comp (ContinuousLinearMap.fst ℝ _ _)).prod (P1.comp (ContinuousLinearMap.snd ℝ _ _))

/-- Second phase block. -/
noncomputable def Q2 : Phase (m + k) →L[ℝ] Phase k :=
  (P2.comp (ContinuousLinearMap.fst ℝ _ _)).prod (P2.comp (ContinuousLinearMap.snd ℝ _ _))

/-- The coordinate shuffle `Phase m × Phase k → Phase (m + k)`. -/
noncomputable def Ψ (z : Phase m) (w : Phase k) : Phase (m + k) :=
  (appendPos z.1 w.1, appendPos z.2 w.2)

lemma Q1_apply (p : Phase (m + k)) : Q1 p = (P1 p.1, P1 p.2) := rfl

lemma Q2_apply (p : Phase (m + k)) : Q2 p = (P2 p.1, P2 p.2) := rfl

lemma Q1_Ψ (z : Phase m) (w : Phase k) : Q1 (Ψ z w) = z := by
  simp [Q1_apply, Ψ, P1_append]

lemma Q2_Ψ (z : Phase m) (w : Phase k) : Q2 (Ψ z w) = w := by
  simp [Q2_apply, Ψ, P2_append]

lemma Ψ_Q (p : Phase (m + k)) : Ψ (Q1 p) (Q2 p) = p := by
  simp [Q1_apply, Q2_apply, Ψ, append_P]

lemma Q_ext {p q : Phase (m + k)} (h1 : Q1 p = Q1 q) (h2 : Q2 p = Q2 q) : p = q := by
  rw [← Ψ_Q p, ← Ψ_Q q, h1, h2]

/-- `Ψ` as a linear equivalence. -/
noncomputable def ΨLe : (Phase m × Phase k) ≃ₗ[ℝ] Phase (m + k) where
  toFun zw := Ψ zw.1 zw.2
  invFun p := (Q1 p, Q2 p)
  map_add' a b := Q_ext (by simp [Q1_Ψ]) (by simp [Q2_Ψ])
  map_smul' c a := Q_ext (by simp [Q1_Ψ]) (by simp [Q2_Ψ])
  left_inv a := by simp [Q1_Ψ, Q2_Ψ]
  right_inv p := Ψ_Q p

noncomputable def ΨL : (Phase m × Phase k) ≃L[ℝ] Phase (m + k) :=
  (ΨLe (m := m) (k := k)).toContinuousLinearEquiv

lemma ΨL_apply (zw : Phase m × Phase k) : ΨL zw = Ψ zw.1 zw.2 := rfl

lemma toReal_half : (2 : ℝ≥0∞)⁻¹.toReal = 1 / 2 := by
  rw [ENNReal.toReal_inv]; norm_num

lemma pprod_eq (X : Set (Phase m)) (Y : Set (Phase k)) :
    symplecticPProduct 2 X Y = ⋃ t ∈ Icc (0 : ℝ) 1,
      ΨL '' ((Real.sqrt (1 - t) • X) ×ˢ (Real.sqrt t • Y)) := by
  simp only [symplecticPProduct, toReal_half, ← Real.sqrt_eq_rpow]
  rfl

lemma mem_pprod_iff {X : Set (Phase m)} {Y : Set (Phase k)} {p : Phase (m + k)} :
    p ∈ symplecticPProduct 2 X Y ↔
      ∃ s τ : ℝ, 0 ≤ s ∧ 0 ≤ τ ∧ s ^ 2 + τ ^ 2 = 1 ∧ Q1 p ∈ s • X ∧ Q2 p ∈ τ • Y := by
  rw [pprod_eq]
  simp only [mem_iUnion]
  constructor
  · rintro ⟨t, ht, zw, ⟨hz, hw⟩, rfl⟩
    refine ⟨Real.sqrt (1 - t), Real.sqrt t, Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_, ?_, ?_⟩
    · rw [Real.sq_sqrt (by linarith [ht.2]), Real.sq_sqrt ht.1]; ring
    · rw [ΨL_apply, Q1_Ψ]; exact hz
    · rw [ΨL_apply, Q2_Ψ]; exact hw
  · rintro ⟨s, τ, hs, hτ, h1, h2, h3⟩
    refine ⟨τ ^ 2, ⟨by positivity, by nlinarith⟩, (Q1 p, Q2 p), ⟨?_, ?_⟩, Ψ_Q p⟩
    · have : 1 - τ ^ 2 = s ^ 2 := by linarith
      rw [this, Real.sqrt_sq hs]; exact h2
    · rw [Real.sqrt_sq hτ]; exact h3

end Viterbo.MS.PartM
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartM
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
lemma smul_subset_smul {X : Set (Phase n)} (hX : Convex ℝ X) (hX0 : (0 : Phase n) ∈ X)
    {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') : s • X ⊆ s' • X := by
  rintro _ ⟨x, hx, rfl⟩
  rcases hs.eq_or_lt with h | h
  · subst h
    exact ⟨0, hX0, by simp⟩
  · have hs' : 0 < s' := lt_of_lt_of_le h hss
    refine ⟨(s / s') • x, hX.smul_mem_of_zero_mem hX0 hx ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_le_one hs']; exact hss
    · simp only [smul_smul]; congr 1; field_simp

lemma add_mem_smul {X : Set (Phase n)} (hX : Convex ℝ X) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    {a b : Phase n} (ha : a ∈ s • X) (hb : b ∈ t • X) : a + b ∈ (s + t) • X := by
  rw [hX.add_smul hs ht]; exact add_mem_add ha hb

lemma smul_mem_smul {X : Set (Phase n)} {s c : ℝ} {a : Phase n} (ha : a ∈ s • X) :
    c • a ∈ (c * s) • X := by
  rw [mul_smul]; exact smul_mem_smul_set ha

end Viterbo.MS.PartM
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartM
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {m k : ℕ}
lemma mem_pprod_of_le {X : Set (Phase m)} {Y : Set (Phase k)} (hX : Convex ℝ X) (hX0 : (0 : Phase m) ∈ X)
    {p : Phase (m + k)} {s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 ≤ τ) (h : s ^ 2 + τ ^ 2 ≤ 1)
    (h1 : Q1 p ∈ s • X) (h2 : Q2 p ∈ τ • Y) : p ∈ symplecticPProduct 2 X Y := by
  rw [mem_pprod_iff]
  refine ⟨Real.sqrt (1 - τ ^ 2), τ, Real.sqrt_nonneg _, hτ, ?_, ?_, h2⟩
  · rw [Real.sq_sqrt (by linarith [sq_nonneg s])]; ring
  · refine smul_subset_smul hX hX0 hs ?_ h1
    exact Real.le_sqrt_of_sq_le (by linarith)

theorem isConvexDomain_pprod {m k : ℕ} (X : Set (Phase m)) (Y : Set (Phase k))
    (hX : IsConvexDomain X) (hY : IsConvexDomain Y) (hX0 : 0 ∈ X) (hY0 : 0 ∈ Y) :
    IsConvexDomain (symplecticPProduct 2 X Y) := by
  refine ⟨?_, ?_, ?_⟩
  · have hsub : symplecticPProduct 2 X Y ⊆ ΨL '' (X ×ˢ Y) := by
      intro p hp
      obtain ⟨s, τ, hs, hτ, h, h1, h2⟩ := mem_pprod_iff.1 hp
      refine ⟨(Q1 p, Q2 p), ⟨?_, ?_⟩, Ψ_Q p⟩
      · have := smul_subset_smul hX.2.1 hX0 hs (s' := 1) (by nlinarith) h1
        rwa [one_smul] at this
      · have := smul_subset_smul hY.2.1 hY0 hτ (s' := 1) (by nlinarith) h2
        rwa [one_smul] at this
    exact (ΨL.toContinuousLinearMap.lipschitz.isBounded_image (hX.1.prod hY.1)).subset hsub
  · intro p hp q hq a b ha hb hab
    obtain ⟨s1, τ1, hs1, hτ1, h1, hp1, hp2⟩ := mem_pprod_iff.1 hp
    obtain ⟨s2, τ2, hs2, hτ2, h2, hq1, hq2⟩ := mem_pprod_iff.1 hq
    apply mem_pprod_of_le hX.2.1 hX0 (s := a * s1 + b * s2) (τ := a * τ1 + b * τ2)
      (by positivity) (by positivity)
    · have : s1 * s2 + τ1 * τ2 ≤ 1 := by nlinarith [sq_nonneg (s1 - s2), sq_nonneg (τ1 - τ2)]
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [mul_nonneg ha hb]
    · rw [map_add, map_smul, map_smul]
      exact add_mem_smul hX.2.1 (by positivity) (by positivity)
        (smul_mem_smul hp1) (smul_mem_smul hq1)
    · rw [map_add, map_smul, map_smul]
      exact add_mem_smul hY.2.1 (by positivity) (by positivity)
        (smul_mem_smul hp2) (smul_mem_smul hq2)
  · obtain ⟨x, hx⟩ := hX.2.2
    obtain ⟨y, hy⟩ := hY.2.2
    set c := Real.sqrt (1 - 1 / 2) with hc
    have hc0 : c ≠ 0 := by rw [hc]; positivity
    have hO : IsOpen (ΨL '' ((c • interior X) ×ˢ (c • interior Y))) :=
      ΨL.toHomeomorph.isOpenMap _
        ((isOpen_interior.smul₀ hc0).prod (isOpen_interior.smul₀ hc0))
    have hsub : ΨL '' ((c • interior X) ×ˢ (c • interior Y)) ⊆ symplecticPProduct 2 X Y := by
      rw [pprod_eq]
      intro p hp
      simp only [mem_iUnion]
      refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      have e : Real.sqrt (1 / 2) = c := by rw [hc]; norm_num
      rw [e]
      exact image_mono (Set.prod_mono (smul_set_mono interior_subset)
        (smul_set_mono interior_subset)) hp
    exact ⟨_, interior_maximal hsub hO ⟨(c • x, c • y),
      ⟨smul_mem_smul_set hx, smul_mem_smul_set hy⟩, rfl⟩⟩

end Viterbo.MS.PartM
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartM
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
lemma hse_of_subset {U V : Set (Phase n)} (h : U ⊆ V) : HasSymplecticEmbedding U V :=
  ⟨id, contDiffOn_id, IsEmbedding.subtypeVal, fun _ hz => h hz, fun _ _ v w => by simp⟩

lemma hse_translate (U : Set (Phase n)) (d : Phase n) :
    HasSymplecticEmbedding U ((fun z => z + d) '' U) := by
  refine ⟨fun z => z + d, (contDiff_id.add contDiff_const).contDiffOn, ?_, mapsTo_image _ _, ?_⟩
  · exact (Homeomorph.addRight d).isEmbedding.comp IsEmbedding.subtypeVal
  · intro z _ v w
    rw [fderiv_add_const, fderiv_fun_id]
    rfl

lemma cap_mono {c : Set (Phase n) → ℝ≥0∞} (hc : IsSymplecticCapacity n c) {U V : Set (Phase n)}
    (h : U ⊆ V) : c U ≤ c V :=
  hc.1 U V (hse_of_subset h)

lemma cap_translate {c : Set (Phase n) → ℝ≥0∞} (hc : IsSymplecticCapacity n c) (U : Set (Phase n))
    (d : Phase n) : c ((fun z => z + d) '' U) = c U := by
  apply le_antisymm
  · have := hc.1 _ _ (hse_translate ((fun z => z + d) '' U) (-d))
    rwa [image_image, show (fun z : Phase n => z + d + -d) = id by funext z; simp,
      image_id] at this
  · exact hc.1 _ _ (hse_translate U d)

lemma isConvexDomain_translate {X : Set (Phase n)} (hX : IsConvexDomain X) (d : Phase n) :
    IsConvexDomain ((fun z => z + d) '' X) := by
  refine ⟨(IsometryEquiv.addRight d).isometry.lipschitz.isBounded_image hX.1, ?_, ?_⟩
  · have := hX.2.1.vadd d
    rwa [← image_vadd, show (fun x : Phase n => d +ᵥ x) = fun z => z + d by
      funext z; rw [vadd_eq_add, add_comm]] at this
  · have e : (fun z => z + d) '' interior X = interior ((fun z => z + d) '' X) :=
      (Homeomorph.addRight d).image_interior X
    rw [← e]
    exact hX.2.2.image _

lemma cEHZ_translate (hn : 1 ≤ n) {X : Set (Phase n)} (hX : IsConvexDomain X) (d : Phase n) :
    cEHZ ((fun z => z + d) '' X) = cEHZ X := by
  obtain ⟨c, hc, hcE⟩ := (exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ n hn).1
  rw [← hcE _ hX, ← hcE _ (isConvexDomain_translate hX d), cap_translate hc]

end Viterbo.MS.PartM
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartM
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
/-! Helpers copied from `Solutions/Viterbo/GromovVol.lean`. -/
theorem ofLp_preimage_capacityBall (n : ℕ) (c : ℝ) :
    (WithLp.ofLp : WithLp 2 (Position n × Position n) → Phase n) ⁻¹' capacityBall n c =
      Metric.ball (0 : WithLp 2 (Position n × Position n)) (Real.sqrt (c / Real.pi)) := by
  ext x
  simp only [Set.mem_preimage, capacityBall, Set.mem_ofPred_eq, mem_ball_zero_iff]
  have hx := WithLp.prod_norm_sq_eq_of_L2 x
  rw [← Real.sqrt_sq (norm_nonneg x)]
  rw [Real.sqrt_lt_sqrt_iff (sq_nonneg _), hx, lt_div_iff₀ Real.pi_pos, mul_comm]
  rfl

theorem volume_capacityBall (n : ℕ) {c : ℝ} (hc : 0 < c) :
    volume (capacityBall n c) = ENNReal.ofReal (c ^ n / n.factorial) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have huniv : capacityBall 0 c = Set.univ := by
      ext z
      simp only [capacityBall, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have h1 : z.1 = 0 := Subsingleton.elim _ _
      have h2 : z.2 = 0 := Subsingleton.elim _ _
      simp [h1, h2, hc]
    rw [huniv, Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod]
    simp [volume_euclideanSpace_eq_dirac]
  · have hopen : IsOpen (capacityBall n c) := by
      apply isOpen_lt (by fun_prop) continuous_const
    rw [← (WithLp.volume_preserving_ofLp (Position n) (Position n)).measure_preimage
      hopen.measurableSet.nullMeasurableSet, ofLp_preimage_capacityBall n c]
    have hfr : Module.finrank ℝ (WithLp 2 (Position n × Position n)) = 2 * n := by
      rw [(WithLp.linearEquiv 2 ℝ (Position n × Position n)).finrank_eq, Module.finrank_prod,
        finrank_euclideanSpace, Fintype.card_fin]
      ring
    have : Nontrivial (WithLp 2 (Position n × Position n)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; omega)
    rw [InnerProductSpace.volume_ball, hfr]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : Real.sqrt (c / Real.pi) ^ (2 * n) = (c / Real.pi) ^ n := by
      rw [pow_mul, Real.sq_sqrt (by positivity)]
    have h2 : Real.sqrt Real.pi ^ (2 * n) = Real.pi ^ n := by
      rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
    have h3 : ((2 * n : ℕ) : ℝ) / 2 + 1 = (n : ℝ) + 1 := by push_cast; ring
    rw [h1, h2, h3, Real.Gamma_nat_eq_factorial, div_pow]
    have hpi : Real.pi ^ n ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp

end Viterbo.MS.PartM
end

section
set_option autoImplicit false
namespace Viterbo.MS.PartM
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo Viterbo.MS
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## New material -/
lemma isOpen_capacityBall' (n : ℕ) (c : ℝ) : IsOpen (capacityBall n c) :=
  isOpen_lt (by fun_prop) continuous_const

lemma convex_capacityBall (n : ℕ) (c : ℝ) : Convex ℝ (capacityBall n c) := by
  have e : capacityBall n c = (WithLp.linearEquiv 2 ℝ (Position n × Position n)).symm ⁻¹'
      ((WithLp.ofLp : WithLp 2 (Position n × Position n) → Phase n) ⁻¹' capacityBall n c) := by
    ext z; simp
  rw [e, ofLp_preimage_capacityBall]
  exact (convex_ball _ _).linear_preimage _

lemma isConvexDomain_capacityBall (n : ℕ) {c : ℝ} (hc : 0 < c) :
    IsConvexDomain (capacityBall n c) := by
  refine ⟨?_, convex_capacityBall n c, ?_⟩
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨Real.sqrt (c / Real.pi), fun z hz => ?_⟩
    have hz' : Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) < c := hz
    have h1 : ‖z.1‖ ^ 2 ≤ c / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]; nlinarith [sq_nonneg ‖z.2‖, Real.pi_pos]
    have h2 : ‖z.2‖ ^ 2 ≤ c / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]; nlinarith [sq_nonneg ‖z.1‖, Real.pi_pos]
    rw [Prod.norm_def]
    exact max_le (Real.le_sqrt_of_sq_le h1) (Real.le_sqrt_of_sq_le h2)
  · rw [(isOpen_capacityBall' n c).interior_eq]
    exact ⟨0, by simp [capacityBall, hc]⟩

lemma zero_mem_capacityBall (n : ℕ) {c : ℝ} (hc : 0 < c) : (0 : Phase n) ∈ capacityBall n c := by
  simp [capacityBall, hc]

lemma cEHZ_capacityBall' (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) :
    cEHZ (capacityBall n c) = ENNReal.ofReal c := by
  have e : c = Real.pi * Real.sqrt (c / Real.pi) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]; field_simp
  rw [e]
  exact cEHZ_capacityBall n hn _ (Real.sqrt_pos.2 (by positivity))

lemma volume_translate (A : Set (Phase n)) (d : Phase n) :
    volume ((fun z => z + d) '' A) = volume A := by
  have e : (fun z => z + d) '' A = (fun z => d + z) '' A := by
    congr 1; funext z; exact add_comm z d
  rw [e, Set.image_add_left, Measure.volume_eq_prod, measure_preimage_add]

lemma sys_translate (hn : 1 ≤ n) {A : Set (Phase n)} (hA : IsConvexDomain A) (d : Phase n) :
    systolicRatio ((fun z => z + d) '' A) = systolicRatio A := by
  unfold systolicRatio
  rw [cEHZ_translate hn hA d, volume_translate]

lemma sys_capacityBall (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) :
    systolicRatio (capacityBall n c) = 1 := by
  unfold systolicRatio
  rw [cEHZ_capacityBall' hn hc, volume_capacityBall n hc]
  have e : (n.factorial : ℝ≥0∞) * ENNReal.ofReal (c ^ n / n.factorial) = ENNReal.ofReal c ^ n := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow hc.le]
    congr 1
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [e]
  exact ENNReal.div_self (pow_ne_zero _ (by simpa using hc)) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

lemma cEHZ_lt_top (hn : 1 ≤ n) {A : Set (Phase n)} (hA : IsConvexDomain A) : cEHZ A < ⊤ := by
  obtain ⟨c, hc, hcE⟩ := (exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ n hn).1
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hA.1
  have hpos : (0 : ℝ) < Real.pi * (2 * R ^ 2 + 1) := by positivity
  have hsub : A ⊆ capacityBall n (Real.pi * (2 * R ^ 2 + 1)) := by
    intro z hz
    have h := hR z hz
    rw [Prod.norm_def] at h
    have h1 : ‖z.1‖ ≤ R := le_trans (le_max_left _ _) h
    have h2 : ‖z.2‖ ≤ R := le_trans (le_max_right _ _) h
    have h1' : ‖z.1‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' : ‖z.2‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    show Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) < Real.pi * (2 * R ^ 2 + 1)
    exact mul_lt_mul_of_pos_left (by linarith) Real.pi_pos
  rw [← hcE _ hA]
  calc c A ≤ c (capacityBall n (Real.pi * (2 * R ^ 2 + 1))) := cap_mono hc hsub
    _ = ENNReal.ofReal (Real.pi * (2 * R ^ 2 + 1)) := by
        rw [hcE _ (isConvexDomain_capacityBall n hpos), cEHZ_capacityBall' hn hpos]
    _ < ⊤ := ENNReal.ofReal_lt_top

lemma sys_le_of_zero_mem (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) {A : Set (Phase n)}
    (hA : IsConvexDomain A) (hA0 : 0 ∈ A) : systolicRatio A ≤ maxSystolicRatio (n + k) := by
  by_cases h0 : cEHZ A = 0
  · have : systolicRatio A = 0 := by
      unfold systolicRatio
      rw [h0, zero_pow (by omega), ENNReal.zero_div]
    rw [this]; exact bot_le
  set r := (cEHZ A).toReal with hr
  have hfin := cEHZ_lt_top hn hA
  have hrpos : 0 < r := ENNReal.toReal_pos h0 hfin.ne
  have hAr : cEHZ A = ENNReal.ofReal r := (ENNReal.ofReal_toReal hfin.ne).symm
  have hB := isConvexDomain_capacityBall k hrpos
  have hP := isConvexDomain_pprod A (capacityBall k r) hA hB hA0 (zero_mem_capacityBall k hrpos)
  have hS := systolicRatio_symplecticPProduct_two n k hn hk A (capacityBall k r) hA hB hA0
    (zero_mem_capacityBall k hrpos) (by rw [cEHZ_capacityBall' hk hrpos, hAr])
  rw [sys_capacityBall hk hrpos, mul_one] at hS
  rw [← hS]
  exact le_iSup₂ (f := fun (A : Set (Phase (n + k))) (_ : IsConvexDomain A) => systolicRatio A) _ hP

theorem mono (hn : 1 ≤ n) : ∀ m, n ≤ m → maxSystolicRatio n ≤ maxSystolicRatio m := by
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact le_rfl
  · refine iSup₂_le fun A hA => ?_
    obtain ⟨a, ha⟩ := hA.2.2
    have hA' := isConvexDomain_translate hA (-a)
    have h0 : (0 : Phase n) ∈ (fun z => z + -a) '' A := ⟨a, interior_subset ha, by simp⟩
    rw [← sys_translate hn hA (-a)]
    exact sys_le_of_zero_mem hn hk hA' h0

end Viterbo.MS.PartM
end

section
namespace Viterbo.MS
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {n : ℕ}
/-! ## Part M: monotonicity in the dimension -/
alias mono := Viterbo.MS.PartM.mono

/-! ## Assembly -/
theorem finite (hn : 1 ≤ n) : maxSystolicRatio n < ⊤ := by
  obtain ⟨C, hC⟩ := systolicRatio_le_const hn
  exact lt_of_le_of_lt (iSup₂_le fun A hA => hC A hA) ENNReal.ofReal_lt_top

theorem main (n : ℕ) (hn : 1 ≤ n) :
    (∀ m, n ≤ m → maxSystolicRatio n ≤ maxSystolicRatio m) ∧ maxSystolicRatio n < ⊤ ∧
      ∃ A : Set (OAI.SymmetricPolar.Phase n), IsConvexDomain A ∧
        systolicRatio A = maxSystolicRatio n :=
  ⟨mono hn, finite hn, attained hn (finite hn)⟩

end Viterbo.MS
end

section
open Viterbo.MS in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (∀ m, n ≤ m → Viterbo.maxSystolicRatio n ≤ Viterbo.maxSystolicRatio m) ∧
      Viterbo.maxSystolicRatio n < ⊤ ∧
      ∃ A : Set (OAI.SymmetricPolar.Phase n), Viterbo.IsConvexDomain A ∧
        Viterbo.systolicRatio A = Viterbo.maxSystolicRatio n :=
  main n hn

end
