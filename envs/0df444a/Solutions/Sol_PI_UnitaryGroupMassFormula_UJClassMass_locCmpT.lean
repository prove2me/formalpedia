-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.locCmpT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:08:54.744521+00:00
-- url     : https://prove2.me/submissions/c3f2634a-5e46-4dc1-b072-bb0411d0876e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PsiInclR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_SigRTmulOne
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_den
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_latHat_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_low_vec
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_one_sub_evT_inv_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) {k : ℕ} (hkpos : 0 < k)
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    (T : Set (HeightOneSpectrum (𝓞 F))) (p : ℕ) (hp0 : p ≠ 0) (hp : p ≠ 1)
    (hpT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → (p : 𝓞 F) ∉ w.asIdeal) (g1 g2 : HA (AF F) σ J)
    (hC : ∀ y ∈ latHat F E L, (evT T ⊗ₜ[F] (1 : E)) • (finMat σ J (g2⁻¹ * g1)).mulVec y ∈ latHat F E L)
    {x : Fin M → E} (hx : x ∈ abelian₂ σ J L g1) : ∃ m2 : ℕ, ¬ p ∣ m2 ∧ (m2 : E) • x ∈ abelian₂ σ J L g2 := by
  classical
  set z := (finMat σ J g2⁻¹).mulVec (vinc (F := F) x) with hz
  have hzC : (evT T ⊗ₜ[F] (1 : E)) • z ∈ latHat F E L := by
    have : z = (finMat σ J (g2⁻¹ * g1)).mulVec ((finMat σ J g1⁻¹).mulVec (vinc (F := F) x)) := by
      rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hC _ hx
  have hden : ∃ m : ℕ, 0 < m ∧ m • z ∈ latHat F E L := by
    choose mf hmf hmO using fun i => den (F := F) (E := E) (z i)
    refine ⟨k * ∏ i, mf i, Nat.mul_pos hkpos (Finset.prod_pos fun i _ => hmf i), ?_⟩
    rw [mul_smul]
    apply low_vec L hk
    intro i
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ i)
    show (∏ i, mf i) • z i ∈ Oh F E
    rw [hq, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (hmO i) _
  obtain ⟨m, hm, hmz⟩ := hden
  obtain ⟨a, m2, hm2, hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp
  refine ⟨m2, hm2, ?_⟩
  show (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) ∈ latHat F E L
  have e2 : (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) = m2 • z := by
    rw [Nat.cast_smul_eq_nsmul, hz]
    have : vinc (F := F) (m2 • x) = m2 • vinc (F := F) x := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_smul]
  rw [e2]
  set c : Af F := (1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) with hc
  have hcI : c ∈ intAf F := one_sub_evT_inv_int T ((p : 𝓞 F) ^ a)
    (fun w hw hpw => hpT w hw (w.isPrime.mem_of_pow_mem a hpw))
  have hpa : algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a) ≠ 0 := by
    rw [map_pow, map_natCast]; exact pow_ne_zero _ (by exact_mod_cast hp0)
  have hA : algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) * ((p : Af F) ^ a) = 1 := by
    rw [show ((p : Af F) ^ a) = algebraMap F (Af F) (algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a)) by simp,
      ← map_mul, inv_mul_cancel₀ hpa, map_one]
  have hsc : (m2 : Af F) = m2 * evT T + c * (m : Af F) := by
    rw [hmeq, hc]; push_cast at hA ⊢
    linear_combination (-(1 - evT T) * (m2 : Af F)) * hA
  have e3 : m2 • z = m2 • ((evT T ⊗ₜ[F] (1 : E)) • z) + (c ⊗ₜ[F] (1 : E)) • (m • z) := by
    have hι := congrArg (Algebra.TensorProduct.includeLeftRingHom : Af F →+* Af F ⊗[F] E) hsc
    simp only [map_add, map_mul, map_natCast] at hι
    rw [← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2 z, ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2,
      ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m z, smul_smul, smul_smul, ← add_smul]
    congr 1
  rw [e3]
  exact add_mem (AddSubgroup.nsmul_mem _ hzC _) (latHat_smul L hcI hmz)
end PI.UnitaryGroupMassFormula.UJClassMass
