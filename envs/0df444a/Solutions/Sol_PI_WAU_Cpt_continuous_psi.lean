-- Prove2me | solution 1 for PI.WAU.Cpt.continuous_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:30:35.948032+00:00
-- url     : https://prove2.me/submissions/c0a0ae53-bc09-4fde-b22e-0700e051c829

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_NatSmulMulEq
import Theorems.Thm_PI_WAU_Cpt_nat_smul_mul_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_Cpt_mulVec_mem_Lf
import Theorems.Thm_PI_WAU_Cpt_psi_mem
import Theorems.Thm_PI_WAU_coord_emb
import Theorems.Thm_PI_WAU_emb_nsmul
import Theorems.Thm_PI_WAU_emb_sub
import Theorems.Thm_PI_WAU_intC_sum
import Theorems.Thm_PI_WAU_isOpen_Ohat
import Theorems.Thm_PI_WAU_ohat_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution (N d D m : ℕ) (hd : 0 < d) (hD : 0 < D) (hm : 0 < m)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j))
    (hmul : ∀ x y : I.E ⊗[I.F] Af I.F, IntC (bs I) x → IntC (bs I) y → IntC (bs I) (m • (x * y))) :
    Continuous (psi I N) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  intro U hU
  have hV : (fun z => psi I N p * z) ⁻¹' U ∈ 𝓝 (1 : I.Gf) := by
    have := (continuous_mul_left (psi I N p)).tendsto 1
    rw [mul_one] at this
    exact this hU
  obtain ⟨g, hg1, hsub⟩ := I.topf_basis _ hV
  have hN1' : ((g * d * D * m : ℕ) : I.F) ≠ 0 := by
    have : 0 < g * d * D * m := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hg1 hd) hD) hm
    exact_mod_cast this.ne'
  let c : I.F := ((g * d * D * m : ℕ) : I.F)⁻¹
  let W : Set (Cset I N) := {p' | ∀ i j k, algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k) ∈ Ohat I.F}
  have hW : W ∈ 𝓝 p := by
    have hWo : IsOpen W := by
      have : W = ⋂ i, ⋂ j, ⋂ k, (fun p' : Cset I N => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)) ⁻¹'
          Ohat I.F := by
        ext; simp [W]
      rw [this]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => ?_
      have h0 : Continuous (fun p' : Cset I N => p'.1.1 i j k) := by fun_prop
      have hc : Continuous (fun p' : Cset I N => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)) :=
        continuous_const.mul (h0.sub continuous_const)
      exact hc.isOpen_preimage _ isOpen_Ohat
    exact hWo.mem_nhds (fun i j k => by simpa using ohat_zero)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hW fun p' hp' => ?_
  have hQM : matOf I p.1.2 * matOf I p.1.1 = 1 := p.2.2.2.1
  let x := (psi I N p)⁻¹ * psi I N p'
  have hxK : x ∈ I.Kset :=
    (Formalism.UG.stabGL I.Lf).mul_mem ((Formalism.UG.stabGL I.Lf).inv_mem (psi_mem I N p)) (psi_mem I N p')
  have hfx : I.fmat x = matOf I p.1.2 * matOf I p'.1.1 := rfl
  have hcond : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (I.fmat x - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    let u : Co I := fun i j k => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)
    have hu : ∀ i j k, u i j k ∈ Ohat I.F := hp'
    have hδ : ∀ i j, matOf I p'.1.1 i j - matOf I p.1.1 i j = (g * d * D * m) • emb (bs I) (u i j) := by
      intro i j
      simp only [matOf]
      rw [← emb_sub, ← emb_nsmul]
      congr 1; funext k
      simp only [u, Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, c]
      rw [← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, mul_inv_cancel₀ hN1', map_one,
        one_mul]
    let w : Fin I.n → I.E ⊗[I.F] Af I.F := fun i => ∑ j, m • (emb (bs I) (u i j) * (D • y j))
    have hw : ∀ i, IntC (bs I) (w i) := fun i => intC_sum _ fun j _ =>
      hmul _ _ (fun k => by rw [coord_emb]; exact hu i j k) (hup y hy j)
    have hdw := hlow w hw
    have hmv : (matOf I p'.1.1 - matOf I p.1.1) *ᵥ y = (g * d) • w := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, hδ, nat_smul_mul_eq I, Pi.smul_apply,
        Finset.smul_sum, w]
    refine ⟨matOf I p.1.2 *ᵥ (d • w), mulVec_mem_Lf I _ p.2.2.2.2.2.2 _ hdw, ?_⟩
    rw [hfx, ← hQM, ← Matrix.mul_sub, ← Matrix.mulVec_mulVec, hmv, mul_smul, Matrix.mulVec_smul,
      Nat.cast_smul_eq_nsmul]
  have hx := hsub ⟨hxK, hcond⟩
  show psi I N p' ∈ U
  have : psi I N p * x = psi I N p' := mul_inv_cancel_left _ _
  rw [← this]; exact hx
end PI.WAU.Cpt
