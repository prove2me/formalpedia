-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:03.287937+00:00
-- url     : https://prove2.me/submissions/53b1cb08-be3b-41eb-bc65-36513779c456

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_sum_perm_of_noninj
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_det_sub_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv
namespace PositivityTheory.Rg.Sw.WR.K.GB.Inv
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) ℂ) (Φ : (Fin n → Fin n × Fin n) → ℂ)
    (hΦ : ∀ r (π : Equiv.Perm (Fin n)), Φ (r ∘ π) = Φ r) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ r : Fin n → Fin n × Fin n, (∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r =
      A.det * B.det * ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (fun t => (σ t, t)) := by
  classical
  have s1 : ∀ r : Fin n → Fin n × Fin n, ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ((∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r) =
      (A.submatrix (fun t => (r t).1) id).det * (∏ t, B (r t).2 t) * Φ r := by
    intro r
    rw [← Matrix.det_transpose, Matrix.det_apply', Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id]
    ring
  have e1 : ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ r : Fin n → Fin n × Fin n, (∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r =
      ∑ r : Fin n → Fin n × Fin n, (A.submatrix (fun t => (r t).1) id).det * (∏ t, B (r t).2 t) * Φ r := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => s1 r
  rw [e1]
  let eP := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin n) (fun _ => Fin n)
  rw [← eP.symm.sum_comp, Fintype.sum_prod_type]
  have e2 : ∀ c : Fin n → Fin n, ∑ d : Fin n → Fin n,
      (A.submatrix (fun t => ((eP.symm (c, d)) t).1) id).det * (∏ t, B ((eP.symm (c, d)) t).2 t) * Φ (eP.symm (c, d)) =
      (A.submatrix c id).det * ∑ d : Fin n → Fin n, (∏ t, B (d t) t) * Φ (fun t => (c t, d t)) := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [eP, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    ring
  simp_rw [e2]
  rw [sum_perm_of_noninj _ (fun c hc => by rw [det_sub_zero A c hc, zero_mul])]
  have e3 : ∀ π : Equiv.Perm (Fin n), (A.submatrix π id).det * ∑ d : Fin n → Fin n,
      (∏ t, B (d t) t) * Φ (fun t => (π t, d t)) =
      ((Equiv.Perm.sign π : ℤ) : ℂ) * A.det * ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i)) := by
    intro π
    rw [Matrix.det_permute]
    have : ∑ d : Fin n → Fin n, (∏ t, B (d t) t) * Φ (fun t => (π t, d t)) =
        ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i)) := by
      refine Fintype.sum_equiv (Equiv.arrowCongr π (Equiv.refl (Fin n))) _ _ fun d => ?_
      have h1 : (fun t => (π t, d t)) = (fun i => (i, (Equiv.arrowCongr π (Equiv.refl (Fin n)) d) i)) ∘ π := by
        funext t; simp [Equiv.arrowCongr_apply]
      rw [h1, hΦ]
      congr 1
      refine Finset.prod_congr rfl fun t _ => ?_
      simp [Equiv.arrowCongr_apply]
    rw [this]
  simp_rw [e3]
  have e4 : ∑ π : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : ℂ) * A.det *
        ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i)) =
      A.det * ∑ e : Fin n → Fin n, (B.submatrix e id).det * Φ (fun i => (i, e i)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Matrix.det_apply' (B.submatrix e id), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [Matrix.submatrix_apply, id]
    ring
  rw [e4, sum_perm_of_noninj _ (fun c hc => by rw [det_sub_zero B c hc, zero_mul])]
  have e5 : ∀ ρ : Equiv.Perm (Fin n), (B.submatrix ρ id).det * Φ (fun i => (i, ρ i)) =
      B.det * (((Equiv.Perm.sign ρ⁻¹ : ℤ) : ℂ) * Φ (fun t => (ρ⁻¹ t, t))) := by
    intro ρ
    rw [Matrix.det_permute, Equiv.Perm.sign_inv]
    have h2 : (fun i => (i, ρ i)) = (fun t => (ρ⁻¹ t, t)) ∘ ρ := by
      funext i; simp
    rw [h2, hΦ]
    ring
  simp_rw [e5, ← Finset.mul_sum]
  rw [Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) (fun ρ => ((Equiv.Perm.sign ρ⁻¹ : ℤ) : ℂ) * Φ (fun t => (ρ⁻¹ t, t)))
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (fun t => (σ t, t))) (fun ρ => rfl)]
  ring
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
