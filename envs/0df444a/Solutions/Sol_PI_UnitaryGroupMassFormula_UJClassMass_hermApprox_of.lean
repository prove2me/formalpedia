-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.hermApprox_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:59.036841+00:00
-- url     : https://prove2.me/submissions/af73bd7b-92a9-4d3f-8722-fd2baace4e96

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermSk
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_matGL
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_locGmapStep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_matGL_mem
import Theorems.Thm_unitary_approximation_finite
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
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (hL : LocSw) (hC : CloseLoc) (hW : WPlace) (hB : BcU) (hG : GramOK) :
    HermApprox := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hS hN hL0 N hNg P hP
  classical
  have hσσ : ∀ e, σ (σ e) = e := fun e => by rw [hσ, hσ, star_star]
  obtain ⟨hH, hdet⟩ := hG F E σ hσ V h M b hS hN
  set J := gramOf h b with hJ
  let K0 : Subfield E := Fix (σ : E →+* E)
  let σ0 : E →ₐ[K0] E := sigFix σ
  have hσ0 : ∀ e, σ0 e = σ e := fun _ => rfl
  have hσσ0 : ∀ e, σ0 (σ0 e) = e := fun e => hσσ e
  have hθ0 : ∃ θ, σ0 θ ≠ θ := hθ
  have hH0 : PI.UnitaryApproxDefs.IsHerm (σ0 : E →+* E) J := hH
  have hfix : ∀ e, σ0 e = e → ∃ c : K0, algebraMap K0 E c = e := fun e he => ⟨⟨e, he⟩, rfl⟩
  have hσstar : ∀ a, σ0 a = star a := fun a => hσ a

  have wit : ∀ p : P, ∃ u ∈ isom h,
      gmap u (loc (K := E) (p : Ideal (𝓞 E)) L0) = loc (K := E) (p : Ideal (𝓞 E)) N :=
    fun p => hNg.2 p (hP p p.2)
  choose u hu hul using wit
  let g : P → GL (Fin M) E := fun p => matGL b (u p)
  have hg : ∀ p, g p ∈ PI.UnitaryApproxDefs.UJ (σ0 : E →+* E) J := fun p => matGL_mem σ hσ h b (hu p)

  let w : P → HeightOneSpectrum (𝓞 K0) := fun p =>
    ⟨(p : Ideal (𝓞 E)).comap (algebraMap (𝓞 K0) (𝓞 E)),
      by have := (hP _ p.2).isPrime; infer_instance, hW K0 E _ (hP _ p.2)⟩
  let T : Finset (HeightOneSpectrum (𝓞 K0)) := Finset.univ.image w
  let gl : (t : HeightOneSpectrum (𝓞 K0)) → GL (Fin M) (E ⊗[K0] t.adicCompletion K0) := fun t =>
    if hx : ∃ p, w p = t then
      Units.map ((PI.UnitaryApproxDefs.inclE (F := K0) (E := E) (t.adicCompletion K0)).mapMatrix :
        Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[K0] t.adicCompletion K0)).toMonoidHom
          (g (Classical.choose hx))
    else 1
  have hgl : ∀ t ∈ T, gl t ∈ PI.UnitaryApproxDefs.UPts σ0 J (t.adicCompletion K0) := by
    intro t _
    by_cases hx : ∃ p, w p = t
    · simp only [gl, dif_pos hx]
      exact hB K0 E σ0 M J _ _ (hg _)
    · simp only [gl, dif_neg hx]
      exact one_mem _

  have hCp := fun p : P => hC K0 E σ0 V M J b L0 hσσ0 hH0 hdet hL0 (g p) (hg p)
  choose D hD0 hDcl using hCp
  let Dall : 𝓞 K0 := ∏ p, D p
  have hDall : Dall ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hD0 p
  obtain ⟨γ, hγ, hc⟩ := unitary_approximation_finite K0 E (Fin M) σ0 J hσσ0 hθ0 hH0 hdet
    T gl hgl Dall hDall
  refine ⟨⟨γ, hγ⟩, fun q hq => ?_⟩
  let q' : P := ⟨q, hq⟩
  have hx : ∃ p, w p = w q' := ⟨q', rfl⟩
  set ps := Classical.choose hx with hps
  have hpw : w ps = w q' := Classical.choose_spec hx
  have hT : w q' ∈ T := Finset.mem_image_of_mem w (Finset.mem_univ _)
  have hcong := hc (w q') hT
  have hglq : gl (w q') = Units.map ((PI.UnitaryApproxDefs.inclE (F := K0) (E := E) ((w q').adicCompletion K0)).mapMatrix :
        Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[K0] (w q').adicCompletion K0)).toMonoidHom
          (g ps) := dif_pos hx
  rw [hglq] at hcong
  have hcl := hDcl ps Dall (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) γ hγ (w q') hcong
  have eq1 := hL K0 E σ0 hσstar hfix V q (hP q hq) (w q') rfl
  have eq2 := hL K0 E σ0 hσstar hfix V (ps : Ideal (𝓞 E)) (hP _ ps.2) (w q') (by rw [← hpw])
  show loc (K := E) q (gmap (linOf b γ) L0) = loc (K := E) q N
  rw [eq1, eq1, hcl, ← eq2, ← eq2, linOf_matGL, locGmapStep E V (u ps) (ps : Ideal (𝓞 E)) L0]
  exact hul ps
end PI.UnitaryGroupMassFormula.UJClassMass
