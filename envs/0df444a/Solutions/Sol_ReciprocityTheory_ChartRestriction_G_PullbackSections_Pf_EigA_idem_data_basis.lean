-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.idem_data_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:15.800401+00:00
-- url     : https://prove2.me/submissions/e6dc1e78-8ba4-4c1f-9ebe-44a5937edb7d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_TBIdemDen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_IdemDataBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_sum_dual_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_dual_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_trace_dual_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
variable {E : Type} [Field E] [NumberField E]
private theorem repr_trDual_lemma {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E)
    (x : E) (j : ι) : (TB.trDual b).repr x j = Algebra.trace ℚ E (x * b j) := by
  have h := LinearMap.BilinForm.dualBasis_repr_apply
    (traceForm_nondegenerate ℚ E) b x j
  rw [Algebra.traceForm_apply] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
theorem _root_.solution {k V : Type} [Field k] [CommRing V] [Algebra V k] (ψ : E →+* k)
    (hint : ∀ x : 𝓞 E, ∃ v : V, algebraMap V k v = ψ (algebraMap (𝓞 E) E x)) (w : V)
    (hw : algebraMap V k w * (((discr E).natAbs : ℕ) : k) = 1) :
    ∃ (b : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E) (c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → V),
      (∑ i, algebraMap V k (c i) * ψ (algebraMap (𝓞 E) E (b i)) = 1) ∧
      ∀ a : 𝓞 E, ∃ m : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ,
        (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap V k (c i) = ψ (algebraMap (𝓞 E) E a) * algebraMap V k (c j) := by
  classical
  set bZ := NumberField.RingOfIntegers.basis E with hbZdef
  set bQ := NumberField.integralBasis E with hbQdef
  have hbQ_apply : ∀ i, bQ i = algebraMap (𝓞 E) E (bZ i) := fun i => NumberField.integralBasis_apply E i
  have hint_tr : ∀ x : 𝓞 E, ∃ g : ℤ, (g : ℚ) = Algebra.trace ℚ E (algebraMap (𝓞 E) E x) := by
    intro x
    have hx : IsIntegral ℤ (algebraMap (𝓞 E) E x) := (Algebra.IsIntegral.isIntegral x).algebraMap
    have ht : IsIntegral ℤ (Algebra.trace ℚ E (algebraMap (𝓞 E) E x)) := Algebra.isIntegral_trace hx
    obtain ⟨g, hg⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 ht
    exact ⟨g, by rw [← hg, eq_intCast]⟩
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℤ,
      ∀ i j, (G i j : ℚ) = Algebra.trace ℚ E (algebraMap (𝓞 E) E (bZ i) * algebraMap (𝓞 E) E (bZ j)) :=
    ⟨fun i j => (hint_tr (bZ i * bZ j)).choose, fun i j => by
      rw [← map_mul]; exact (hint_tr (bZ i * bZ j)).choose_spec⟩
  have hD : G.det = NumberField.discr E := by
    have hm : (Int.castRingHom ℚ).mapMatrix G = Algebra.traceMatrix ℚ bQ := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        hbQ_apply, hbQ_apply, ← hG]
      simp
    have h1 : ((G.det : ℤ) : ℚ) = (NumberField.discr E : ℚ) := by
      rw [NumberField.coe_discr, ← hbQdef, Algebra.discr_def, ← hm, ← RingHom.map_det]
      simp
    exact_mod_cast h1
  obtain ⟨z, hzdef⟩ : ∃ z : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E,
      ∀ i, z i = ∑ j, G.adjugate i j • bZ j := ⟨_, fun i => rfl⟩
  have key : ∀ i k, Algebra.trace ℚ E (algebraMap (𝓞 E) E (z i) * bQ k) = if i = k then (G.det : ℚ) else 0 := by
    intro i k
    have h1 : (G.adjugate * G) i k = if i = k then G.det else 0 := by
      rw [Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h2 : Algebra.trace ℚ E (algebraMap (𝓞 E) E (z i) * bQ k) = (((G.adjugate * G) i k : ℤ) : ℚ) := by
      rw [hzdef, hbQ_apply, Matrix.mul_apply, map_sum, Finset.sum_mul, map_sum, Int.cast_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zsmul, smul_mul_assoc, map_zsmul, ← hG, zsmul_eq_mul, Int.cast_mul]
    rw [h2, h1]
    split_ifs <;> simp
  have hz : ∀ i, algebraMap (𝓞 E) E (z i) = (G.det : E) * TB.trDual bQ i := by
    intro i
    apply (TB.trDual bQ).ext_elem
    intro j
    rw [repr_trDual_lemma, repr_trDual_lemma, key i j, mul_assoc, ← zsmul_eq_mul, map_zsmul, trace_dual_mul bQ i j]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij), smul_zero]
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε * G.det = (((NumberField.discr E).natAbs : ℕ) : ℤ) := by
    rw [hD]
    rcases Int.natAbs_eq (NumberField.discr E) with h | h
    · exact ⟨1, by linarith⟩
    · exact ⟨-1, by linarith⟩
  choose v hv using fun i => hint ((ε : 𝓞 E) * z i)
  have hc : ∀ i, algebraMap V k (w * v i) = ψ (TB.trDual bQ i) := by
    intro i
    have e1 : algebraMap (𝓞 E) E ((ε : 𝓞 E) * z i) =
        (((NumberField.discr E).natAbs : ℕ) : E) * TB.trDual bQ i := by
      rw [map_mul, map_intCast, hz i, ← mul_assoc, ← Int.cast_mul, hε, Int.cast_natCast]
    rw [map_mul, hv i, e1, map_mul, map_natCast, ← mul_assoc, hw, one_mul]
  refine ⟨bZ, fun i => w * v i, ?_, ?_⟩
  · rw [← map_one ψ, ← sum_dual_mul bQ, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hc i, map_mul, hbQ_apply]
  · intro a
    refine ⟨fun i j => bZ.repr (a * bZ i) j, fun i => (bZ.sum_repr (a * bZ i)).symm, fun j => ?_⟩
    have hm : ∀ i, Algebra.trace ℚ E (algebraMap (𝓞 E) E a * TB.trDual bQ j * bQ i) =
        ((bZ.repr (a * bZ i) j : ℤ) : ℚ) := by
      intro i
      have hs := bZ.sum_repr (a * bZ i)
      rw [mul_comm (algebraMap (𝓞 E) E a), mul_assoc, hbQ_apply i, ← map_mul (algebraMap (𝓞 E) E)]
      conv_lhs => rw [← hs]
      rw [map_sum, Finset.mul_sum, map_sum]
      simp only [map_zsmul, mul_smul_comm, ← hbQ_apply, trace_dual_mul]
      simp
    simp only [hc]
    rw [← map_mul ψ, dual_expand bQ (algebraMap (𝓞 E) E a * TB.trDual bQ j), map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hm i, Int.cast_smul_eq_zsmul, map_zsmul, zsmul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
