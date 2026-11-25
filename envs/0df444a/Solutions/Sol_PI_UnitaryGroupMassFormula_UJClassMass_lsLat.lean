-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.lsLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:25:24.045186+00:00
-- url     : https://prove2.me/submissions/d802db62-4dbe-4cbf-9c9e-ce0106211e6f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LsLat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UJClassFin_mulVec_single__bf9be0aca3c7
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Oh_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_den_mat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_fg_of_den
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_low_nat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_low_vec
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_oh_inter
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_up_Oh
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_up_nat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crdBounds
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_latHat_incl_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_vinc_smul
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
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution : LSLat := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig g
  set L := crdOf b L0 with hLdef
  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL
  obtain ⟨u, hu, hu'⟩ := up_nat L ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat L ⟨c2, hc2, hlow⟩
  set P := finMat σ (gramOf h b) g⁻¹ with hP
  set Q := finMat σ (gramOf h b) g with hQ
  have hQP : Q * P = 1 := by rw [hQ, hP, ← finMat_mul, mul_inv_cancel, finMat_one]

  have hsm : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ abelian₂ σ (gramOf h b) L g, e • x ∈ abelian₂ σ (gramOf h b) L g := by
    intro e he x hx
    show P.mulVec (vinc (F := F) (e • x)) ∈ latHat F E L
    rw [vinc_smul, Matrix.mulVec_smul]
    exact latHat_incl_smul b L0 he hx
  let C : Submodule (𝓞 E) (Fin M → E) :=
    { carrier := abelian₂ σ (gramOf h b) L g
      add_mem' := fun {x y} hx hy => (LamG σ (gramOf h b) L g).add_mem hx hy
      zero_mem' := (LamG σ (gramOf h b) L g).zero_mem
      smul_mem' := fun c x hx => by
        show (algebraMap (𝓞 E) E c) • x ∈ abelian₂ σ (gramOf h b) L g
        exact hsm _ c.isIntegral_coe x hx }

  obtain ⟨m, hm, hmO⟩ := den_mat (F := F) (E := E) Q
  have hupC : ∀ y ∈ C, ∀ j, IsIntegral ℤ (((m * u : ℕ) : E) * y j) := by
    intro y hy j
    apply oh_inter (F := F)
    have hw : P.mulVec (vinc (F := F) y) ∈ latHat F E L := hy
    have ev : vinc (F := F) y = Q.mulVec (P.mulVec (vinc (F := F) y)) := by
      rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
    have e1 : inclR (F := F) (Af F) (((m * u : ℕ) : E) * y j) =
        ∑ l, (m • Q j l) * (u • P.mulVec (vinc (F := F) y) l) := by
      have : inclR (F := F) (Af F) (((m * u : ℕ) : E) * y j) = (m * u) • vinc (F := F) y j := by
        simp [vinc, nsmul_eq_mul]
      have gen : ∀ w : Fin M → Af F ⊗[F] E,
          (m * u) • Q.mulVec w j = ∑ l, (m • Q j l) * (u • w l) := by
        intro w
        simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, nsmul_eq_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        push_cast
        ring
      rw [this, ← gen, ← ev]
    rw [e1]
    exact AddSubgroup.sum_mem _ fun l _ => Oh_mul (hmO j l) (up_Oh L hu' hw l)
  have hCfg : C.FG := fg_of_den C (m * u) (Nat.mul_pos hm hu) hupC

  obtain ⟨m', hm', hmO'⟩ := den_mat (F := F) (E := E) P
  set c : E := ((k * m' : ℕ) : E) with hc
  have hcne : c ≠ 0 := by rw [hc]; exact_mod_cast (Nat.mul_pos hk hm').ne'
  have hlowC : ∀ i, (Pi.single i c : Fin M → E) ∈ abelian₂ σ (gramOf h b) L g := by
    intro i
    show P.mulVec (vinc (F := F) (Pi.single i c)) ∈ latHat F E L
    have e1 : vinc (F := F) (Pi.single i c) = Pi.single i (inclR (F := F) (Af F) c) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [vinc]
      · simp [vinc, Pi.single_apply, hj]
    have e2 : P.mulVec (Pi.single i (inclR (F := F) (Af F) c)) = k • fun l => m' • P l i := by
      rw [mulVec_single']
      funext l
      simp only [Pi.smul_apply, hc, map_natCast, nsmul_eq_mul]
      push_cast
      ring
    rw [e1, e2]
    exact low_vec L hk' fun l => hmO' l i

  let f : (Fin M → E) →ₗ[𝓞 E] V := (b.equivFun.symm : (Fin M → E) →ₗ[E] V).restrictScalars (𝓞 E)
  let N : Submodule (𝓞 E) V := C.map f
  have hNset : (N : Set V) = latSet σ (gramOf h b) b L0 g := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      show b.equivFun (b.equivFun.symm x) ∈ abelian₂ σ (gramOf h b) L g
      rw [LinearEquiv.apply_symm_apply]; exact hx
    · intro hv
      exact ⟨b.equivFun v, hv, by simp [f]⟩
  refine ⟨N, hNset, ⟨hCfg.map f, ?_⟩⟩
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hb : c • b i ∈ (N : Set V) := by
    rw [hNset]
    show b.equivFun (c • b i) ∈ abelian₂ σ (gramOf h b) L g
    have : b.equivFun (c • b i) = Pi.single i c := by
      funext j
      rw [LinearEquiv.map_smul, Pi.smul_apply, b.equivFun_self]
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj, Ne.symm hj]
    rw [this]; exact hlowC i
  have : b i = c⁻¹ • (c • b i) := by rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hb)
end PI.UnitaryGroupMassFormula.UJClassMass
