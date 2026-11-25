-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isRegularLocalRing_locAt_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:56:12.433865+00:00
-- url     : https://prove2.me/submissions/6fc5d4f2-1177-41ba-9b4e-912f030088fe

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_locAt_chart
import Theorems.Thm_ReciprocityTheory_AnForm_R_finrank_cotangentSpace_locAt
import Theorems.Thm_ReciprocityTheory_AnForm_R_locAt_isLocalRing_isNoetherian
import Theorems.Thm_ReciprocityTheory_AnForm_R_sum_blockWt_eval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
set_option maxHeartbeats 400000
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    {t : ℕ} (G : Fin t → MvPolynomial (Σ k, ι k) ℂ) (hG : ∀ i, ∃ a, IsMultiHomog (G i) a)
    (hspan : Ideal.span (Set.range G) = P)
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ h ∈ chartIdeal P p, eval z h = 0)
    (a : Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) → Fin t)
    (b : Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) → Σ k, ι k)
    (hab : eval z (Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))) ≠ 0) :
    IsRegularLocalRing (locAt (chartIdeal P p) z) := by
  classical
  have hP : IsMultiHomogIdeal P := ⟨Set.range G, by rintro _ ⟨i, rfl⟩; exact hG i, hspan.symm⟩
  have hGP : ∀ i, G i ∈ P := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hGI : ∀ i, G i ∈ chartIdeal P p := fun i => Ideal.mem_sup_left (hGP i)
  have hXI : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p := fun k =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  have hz1 : ∀ k, z ⟨k, p k⟩ = 1 := fun k => by
    have h := hz _ (hXI k)
    simpa [sub_eq_zero] using h
  obtain ⟨hloc, hnoeth⟩ := locAt_isLocalRing_isNoetherian (chartIdeal P p) z hz
  have hcot := finrank_cotangentSpace_locAt (chartIdeal P p) z
  have hd := ringKrullDim_locAt_chart P hP e hdim p z hz
  let grad : MvPolynomial (Σ k, ι k) ℂ → (Σ k, ι k) → ℂ := fun h j => eval z (pderiv j h)
  let v : Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) ⊕ K → (Σ k, ι k) → ℂ :=
    Sum.elim (fun i => grad (G (a i))) (fun k => grad (X ⟨k, p k⟩ - 1))
  let lam : K → ((Σ k, ι k) → ℂ) →ₗ[ℂ] ℂ := fun k =>
    { toFun := fun w => ∑ q, (blockWt k q : ℂ) * (z q * w q)
      map_add' := fun w w' => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c w => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hlam : ∀ k w, lam k w = ∑ q, (blockWt k q : ℂ) * (z q * w q) := fun _ _ => rfl
  have hlamG : ∀ k i, lam k (grad (G i)) = 0 := by
    intro k i
    obtain ⟨dg, hdg⟩ := hG i
    rw [hlam]
    exact (sum_blockWt_eval hdg k z).trans (by rw [hz _ (hGI i), mul_zero])
  have hlamX : ∀ k k', lam k (grad (X ⟨k', p k'⟩ - 1)) = if k' = k then 1 else 0 := by
    intro k k'
    rw [hlam, Finset.sum_eq_single ⟨k', p k'⟩]
    · simp [grad, blockWt, hz1]
    · intro q _ hq
      simp [grad, Ne.symm hq]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    have hK : ∀ k, g (Sum.inr k) = 0 := by
      intro k
      have h := congrArg (lam k) hg
      simp only [map_add, map_sum, map_smul, map_zero, smul_eq_mul, v, Sum.elim_inl, Sum.elim_inr,
        hlamG, hlamX, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      exact h
    have hg2 : ∑ i, g (Sum.inl i) • grad (G (a i)) = 0 := by
      simpa only [v, Sum.elim_inl, Sum.elim_inr, hK, zero_smul, Finset.sum_const_zero, add_zero]
        using hg
    let M : Matrix (Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K))) (Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K))) ℂ := Matrix.of fun i j => eval z (pderiv (b j) (G (a i)))
    have hM : M.det ≠ 0 := by
      rw [RingHom.map_det] at hab
      convert hab using 2
      ext i j
      simp [M, RingHom.mapMatrix_apply]
    have hvec : Matrix.vecMul (fun i => g (Sum.inl i)) M = 0 := by
      funext j
      have h := congrFun hg2 (b j)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, grad] at h
      simpa only [Matrix.vecMul, dotProduct, M, Matrix.of_apply, Pi.zero_apply] using h
    have hFin : ∀ i, g (Sum.inl i) = 0 := by
      intro i
      by_contra hi
      exact hM (Matrix.exists_vecMul_eq_zero_iff.mp
        ⟨fun i => g (Sum.inl i), fun h => hi (congrFun h i), hvec⟩)
    rintro (i | k)
    · exact hFin i
    · exact hK k
  have hmem : ∀ x, v x ∈ jacSpanAt (chartIdeal P p) z := by
    rintro (i | k)
    · exact Submodule.subset_span ⟨G (a i), hGI (a i), rfl⟩
    · exact Submodule.subset_span ⟨_, hXI k, rfl⟩
  have hrank : (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) + Fintype.card K ≤ Module.finrank ℂ (jacSpanAt (chartIdeal P p) z) := by
    let v' : Fin (Fintype.card (Σ k, ι k) - (e + Fintype.card K)) ⊕ K → jacSpanAt (chartIdeal P p) z := fun x => ⟨v x, hmem x⟩
    have hv' : LinearIndependent ℂ v' := LinearIndependent.of_comp (jacSpanAt _ _).subtype hv
    simpa using hv'.fintype_card_le_finrank
  have hcotle : Module.finrank (ResidueField (locAt (chartIdeal P p) z))
      (CotangentSpace (locAt (chartIdeal P p) z)) ≤ e := by
    omega
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hd]
  exact_mod_cast hcotle
end ReciprocityTheory.AnForm.R
