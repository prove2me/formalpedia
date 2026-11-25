-- Prove2me | solution 1 for PI.ScRefExists.GWG.side_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:52.353593+00:00
-- url     : https://prove2.me/submissions/3ace7f78-5872-494f-a01c-ede8ed325765

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
import Theorems.Thm_PI_ScRefExists_GWG_theta_mem
import Theorems.Thm_PI_ScRefExists_GWG_osmul_mem
import Theorems.Thm_PI_ScRefExists_GWG_gL_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
namespace PI.ScRefExists.GWG
open PI.ScRefExists.Sk
section Lemmas
variable (I : Formalism.MainNotions.S.AutInst)
private theorem star_coe_mem_range_algebraMap (θ : 𝓞 I.E) :
    star (θ : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := by
  have h : IsIntegral ℤ (star (θ : I.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom
  exact ⟨⟨star (θ : I.E), h⟩, rfl⟩
end Lemmas
end PI.ScRefExists.GWG
end
end

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GWG
theorem _root_.solution {r k M : ℕ} (e f : Fin r → Fin I.n → I.E) (θ : 𝓞 I.E) (G ga : ℕ) (qa qb w wab : ℤ)
    (z za zb : Fin I.n → I.E) (b ba bb bd bda bdb : Fin k → Fin I.n → I.E)
    (hza : za ∈ I.L) (hzb : zb ∈ I.L)
    (hbL : ∀ i, ba i ∈ I.L ∧ bb i ∈ I.L ∧ bda i ∈ I.L ∧ bdb i ∈ I.L)
    (hsum : (qa : I.E) + (qb : I.E) = 1) (hprod : (qa : I.E) * (qb : I.E) = (G : I.E) * (wab : I.E))
    (hga : (qa : I.E) * (ga : I.E) = (G : I.E) * (w : I.E))
    (hz : z = qa • za + qb • zb) (hb : ∀ i, b i = qa • ba i + qb • bb i)
    (hbd : ∀ i, bd i = qa • bda i + qb • bdb i) {y : Fin I.n → I.E}
    (hsp : y ∈ Submodule.span (𝓞 I.E) (SS I r k M e f θ za ba bda) ⊔ gL I ga) :
    qa • y ∈ Submodule.span (𝓞 I.E) (SS I r k M e f θ z b bd) ⊔ gL I G := by
  set S' := Submodule.span (𝓞 I.E) (SS I r k M e f θ z b bd) ⊔ gL I G with hS'
  have hsp' : ∀ v ∈ SS I r k M e f θ z b bd, v ∈ S' :=
    fun v hv => Submodule.mem_sup_left (Submodule.subset_span hv)
  have hG' : ∀ x ∈ I.L, (G : I.E) • x ∈ S' := fun x hx => Submodule.mem_sup_right (gL_mem I G hx)
  have hzs : ∀ (q : ℤ) {v : Fin I.n → I.E}, v ∈ S' → q • v ∈ S' := fun q v hv => zsmul_mem hv q
  have hwab : (wab : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := ⟨(wab : 𝓞 I.E), by simp⟩
  let φ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
    { toFun := fun v => qa • v
      map_add' := fun a c => smul_add qa a c
      map_smul' := fun c v => smul_comm qa c v }
  suffices h : Submodule.span (𝓞 I.E) (SS I r k M e f θ za ba bda) ⊔ gL I ga ≤ S'.comap φ from h hsp
  apply sup_le
  · rw [Submodule.span_le]
    intro v hv
    simp only [SS, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hv
    show qa • v ∈ S'
    rcases hv with ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | hvz) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact hzs qa (hsp' _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩)))))
    · exact hzs qa (hsp' _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))))
    · rw [hvz]
      have hv : qa • za = qa • z + (G : I.E) • ((wab : I.E) • (za - zb)) := by
        ext j
        simp only [hz, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
        linear_combination (za j - zb j) * hprod - ((qa : I.E) * za j) * hsum
      rw [hv]
      exact S'.add_mem (hzs qa (hsp' z (Or.inl (Or.inl (Or.inr rfl)))))
        (hG' _ (osmul_mem I hwab (I.L.sub_mem hza hzb)))
    · have hv : qa • ((θ : I.E) • ba i) = qa • ((θ : I.E) • b i) +
          (G : I.E) • ((wab : I.E) • ((θ : I.E) • (ba i - bb i))) := by
        ext j
        simp only [hb, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
        linear_combination (θ : I.E) * (ba i j - bb i j) * hprod - ((θ : I.E) * (qa : I.E) * ba i j) * hsum
      rw [hv]
      exact S'.add_mem (hzs qa (hsp' _ (Or.inl (Or.inr ⟨i, rfl⟩))))
        (hG' _ (osmul_mem I hwab (osmul_mem I (theta_mem I θ) (I.L.sub_mem (hbL i).1 (hbL i).2.1))))
    · have hv : qa • (star (θ : I.E) • bda i) = qa • (star (θ : I.E) • bd i) +
          (G : I.E) • ((wab : I.E) • (star (θ : I.E) • (bda i - bdb i))) := by
        ext j
        simp only [hbd, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
        linear_combination star (θ : I.E) * (bda i j - bdb i j) * hprod -
          (star (θ : I.E) * (qa : I.E) * bda i j) * hsum
      rw [hv]
      exact S'.add_mem (hzs qa (hsp' _ (Or.inr ⟨i, rfl⟩)))
        (hG' _ (osmul_mem I hwab (osmul_mem I (star_coe_mem_range_algebraMap I θ)
          (I.L.sub_mem (hbL i).2.2.1 (hbL i).2.2.2))))
  · rw [gL, Submodule.span_le]
    rintro v ⟨x, hx, rfl⟩
    show qa • ((ga : I.E) • x) ∈ S'
    have hv : qa • ((ga : I.E) • x) = (G : I.E) • ((w : I.E) • x) := by
      ext j
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
      linear_combination (x j) * hga
    rw [hv]
    exact hG' _ (osmul_mem I ⟨(w : 𝓞 I.E), by simp⟩ hx)
end PI.ScRefExists.GWG
