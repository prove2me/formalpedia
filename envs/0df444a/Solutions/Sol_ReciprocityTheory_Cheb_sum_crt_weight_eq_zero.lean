-- Prove2me | solution 1 for ReciprocityTheory.Cheb.sum_crt_weight_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:24.197207+00:00
-- url     : https://prove2.me/submissions/5ce40930-41a7-4b30-bacc-dbf90fcfa747

import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormCongr
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {R : Type*} [CommRing R] (I C : Ideal R) (hIC : IsCoprime I C)
    [Fintype (R ⧸ I * C)] [Fintype (R ⧸ I)] [Fintype (R ⧸ C)] (f : R → ℂ)
    (hf : ∀ a b, a - b ∈ I → f a = f b) (σ : R ⧸ I * C → R)
    (hσ : ∀ y, Ideal.Quotient.mk _ (σ y) = y) :
    ∑ y, f (σ y) * (1 - (Fintype.card (R ⧸ C) : ℂ) * if σ y ∈ C then 1 else 0) = 0 := by
  set e := Ideal.quotientMulEquivQuotientProd I C hIC
  have hfst : ∀ p, Ideal.Quotient.mk I (σ (e.symm p)) = p.1 := by
    intro p
    have := congrArg Prod.fst (e.apply_symm_apply p)
    rw [← hσ (e.symm p), Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk] at this
    exact this
  have hsnd : ∀ p, Ideal.Quotient.mk C (σ (e.symm p)) = p.2 := by
    intro p
    have := congrArg Prod.snd (e.apply_symm_apply p)
    rw [← hσ (e.symm p), Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk] at this
    exact this
  rw [← (e.symm.toEquiv).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun u _ => ?_
  have hfe : ∀ v, f (σ (e.symm (u, v))) = f (σ (e.symm (u, 0))) := by
    intro v
    apply hf
    rw [← Ideal.Quotient.eq, hfst, hfst]
  have hC : ∀ v, σ (e.symm (u, v)) ∈ C ↔ v = 0 := by
    intro v
    rw [← Ideal.Quotient.eq_zero_iff_mem, hsnd]
  calc ∑ v, f (σ (e.symm.toEquiv (u, v))) *
        (1 - (Fintype.card (R ⧸ C) : ℂ) * if σ (e.symm.toEquiv (u, v)) ∈ C then 1 else 0)
      = ∑ v : R ⧸ C, f (σ (e.symm (u, 0))) *
        (1 - (Fintype.card (R ⧸ C) : ℂ) * if v = 0 then 1 else 0) :=
        Finset.sum_congr rfl fun v _ => by
          simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]
          rw [hfe v]
          simp only [hC v]
    _ = f (σ (e.symm (u, 0))) * ∑ v : R ⧸ C, (1 - (Fintype.card (R ⧸ C) : ℂ) * if v = 0 then 1 else 0) := by
        rw [Finset.mul_sum]
    _ = 0 := by
        simp [Finset.sum_sub_distrib]
end ReciprocityTheory.Cheb
