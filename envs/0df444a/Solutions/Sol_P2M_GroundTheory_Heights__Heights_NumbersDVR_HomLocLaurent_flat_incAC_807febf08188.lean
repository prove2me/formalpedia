-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_flat_incAC_807febf08188
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:35.993014+00:00
-- url     : https://prove2.me/submissions/0d7df2bd-0858-4492-b06a-fc5134d6171d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_ev_comp_psiQ_1dd9a2bf17de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isLocalization_lau_f48fa42d9057

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]
  (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
include hT
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
theorem _root_.solution (hPh : IsMultiHomogIdeal P) :
    letI := (incAC hPW).toAlgebra
    Module.Flat (homLocRing P W) (locC hPW) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  letI : Algebra (MRing ι R ⧸ P) (Lau P W) := (psiQ T hPW hT hPh).toAlgebra
  haveI := isLocalization_lau T hPW hT hPh
  letI : Algebra (Lau P W) (locC hPW) := (evC T hPW hT).toAlgebra
  haveI : IsScalarTower (MRing ι R ⧸ P) (Lau P W) (locC hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      apply Subtype.ext
      change algebraMap _ (FractionRing _) x = ev T hPW hT (psiQ T hPW hT hPh x)
      rw [← RingHom.comp_apply, ev_comp_psiQ]
  have hle : homSub (K := K) P W ≤ (W.map (Ideal.Quotient.mk P)).primeCompl := by
    rintro _ ⟨b, f, -, hfW, rfl⟩ h
    exact hfW ((Ideal.mem_quotient_iff_mem hPW).mp h)
  haveI := IsLocalization.isLocalization_of_submonoid_le (Lau P W) (locC hPW)
    (homSub (K := K) P W) _ hle
  haveI : Module.Flat (Lau P W) (locC hPW) := IsLocalization.flat (locC hPW)
    ((W.map (Ideal.Quotient.mk P)).primeCompl.map (algebraMap (MRing ι R ⧸ P) (Lau P W)))
  haveI : Module.Free (homLocRing P W) (Lau P W) :=
    Module.Free.of_basis (AddMonoidAlgebra.basis (K → ℤ) (homLocRing P W))
  haveI : Module.Flat (homLocRing P W) (Lau P W) := Module.Flat.of_free
  letI := (incAC hPW).toAlgebra
  haveI : IsScalarTower (homLocRing P W) (Lau P W) (locC hPW) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      apply Subtype.ext
      change (a : FractionRing _) = ev T hPW hT (algebraMap (homLocRing P W) (Lau P W) a)
      rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, ev_single]
      simp
  exact Module.Flat.trans (homLocRing P W) (Lau P W) (locC hPW)
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
