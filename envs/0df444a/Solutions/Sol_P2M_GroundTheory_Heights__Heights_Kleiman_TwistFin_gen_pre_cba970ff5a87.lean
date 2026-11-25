-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_gen_pre_cba970ff5a87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:11.027267+00:00
-- url     : https://prove2.me/submissions/02763edf-7c4d-43e9-a99f-4897a6780bc5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_map_C_mem_monos_9cd0e7dd150b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_TMod_de0adca7095b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_mk_eq_9e340803afc7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_map_C_3e351123070f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_of_isHomogeneous_43e37c81185f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_tgr_1d4f2bbc1844


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)
variable (M0 : FinGradedSub (S := S) (x := x) Ω)
variable {n0 d0 g0}
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) (b : ℕ) {ω : Ω}
    (hω : ω ∈ genSet x η S M0 (toChart x I hI) b) :
    ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) ω) := by
  obtain ⟨f, e, h, m, a, t, e', hf, hh, hm, ht, hte, hee, rfl⟩ := hω
  let mm : TMod x η S n0 d0 g0 := ⟨_, single_mem_TMod x η S n0 d0 g0 M0 hspan hm⟩
  let p : Poly (Sy S r) N := MvPolynomial.map (C : S →+* Sy S r) f * C h
  have hp : p.IsHomogeneous e := by
    simpa using (hf.map (C : S →+* Sy S r)).mul (isHomogeneous_C (Fin (N + 1)) h)
  have hmm : mm ∈ (tgraded x η S n0 d0 g0).piece a := by
    change toA x η ((toA x η).symm _) ∈ tgr a
    rw [AddEquiv.apply_symm_apply]
    exact single_mem_tgr _ _ _
  have hpm := (tgraded x η S n0 d0 g0).smul_mem e a p mm hp hmm
  let s : monos (S := Sy S r) I.1 := ⟨MvPolynomial.map (C : S →+* Sy S r) t, map_C_mem_monos S ht⟩
  refine ⟨(LocalizedModule.mk (p • mm) s : LocalizedModule (monos (S := Sy S r) I.1) (TMod x η S n0 d0 g0)),
    Submodule.subset_span ⟨p • mm, s, a + e, e', hpm, hte.map _, by omega, rfl⟩, ?_⟩
  apply locL_mk_eq
  rw [AddEquiv.apply_symm_apply]
  change phi x η S (MvPolynomial.map (C : S →+* Sy S r) t) * _ = toA x η (p • (mm : Amb x η))
  rw [toA_smulP, AddEquiv.apply_symm_apply, phi_map_C x η S hte, map_mul, phi_map_C x η S hf, phi_C,
    psi_of_isHomogeneous η S hh]
  simp only [single_mul_single]
  have ht0 := eval_ne_zero_of_mem_monos (toChart x I hI) ht
  congr 1
  · ext
    · simp; omega
    · simp
  · field_simp
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
