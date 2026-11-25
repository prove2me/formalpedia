-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AffPres.existsUnique_closed_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:34:01.122456+00:00
-- url     : https://prove2.me/submissions/addefa6f-c8f2-4049-ac70-acfe8ab27a36

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_isClosed_of_comap_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_mk_mem_ptQ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres
variable (P : AffPres s)
namespace ReciprocityTheory.AnForm.R.AffPres
theorem _root_.solution (p : Fin P.n → ℂ) (hp : ∀ h ∈ P.K, eval p h = 0) :
    ∃! x : W, ∃ hx : x ∈ P.V, IsClosed {x} ∧ P.coord x hx = p := by
  classical
  have hK : P.K ≤ ptIdeal p := by
    intro h hh
    simp only [ptIdeal, RingHom.mem_ker]
    exact hp h hh
  let y : Spec (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)) :=
    (⟨ptQ P.K p, ptQ_isPrime hK⟩ : PrimeSpectrum (MvPolynomial (Fin P.n) ℂ ⧸ P.K))
  let v : P.V := (Scheme.homeoOfIso P.iso).symm y
  have hv : P.iso.hom.base v = y := (Scheme.homeoOfIso P.iso).apply_symm_apply y
  have hcoordEq : ∀ (z : W) (hz : z ∈ P.V), IsClosed {z} → P.ptOf z hz = ptIdeal p →
      P.coord z hz = p := by
    intro z hz hzc h
    have h' : ptIdeal (P.coord z hz) = ptIdeal p := (P.ptOf_eq_ptIdeal z hz hzc).symm.trans h
    funext j
    have hm : X j - C (p j) ∈ ptIdeal (P.coord z hz) := by
      rw [h']
      simp [ptIdeal]
    simp only [ptIdeal, RingHom.mem_ker] at hm
    simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at hm
    exact sub_eq_zero.mp hm
  have hptv : P.ptOf v.1 v.2 = ptIdeal p := by
    ext h
    show Ideal.Quotient.mk P.K h ∈ (P.iso.hom.base v).asIdeal ↔ _
    rw [hv]
    exact mk_mem_ptQ hK h
  have hclv : IsClosed ({v.1} : Set W) :=
    StalkLocB.isClosed_of_comap_eq (s := s) (hover := P.hover) (v := v) (p := p) (hp := hptv)
  refine ⟨v.1, ⟨v.2, hclv, hcoordEq v.1 v.2 hclv hptv⟩, ?_⟩
  rintro x' ⟨hx', hcl', hco'⟩
  have h1 : P.ptOf x' hx' = ptIdeal p := by rw [P.ptOf_eq_ptIdeal x' hx' hcl', hco']
  have h2 : P.iso.hom.base ⟨x', hx'⟩ = y := by
    apply PrimeSpectrum.ext
    show _ = ptQ P.K p
    unfold ptQ
    rw [← h1]
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  have h3 : (⟨x', hx'⟩ : P.V) = v := (Scheme.homeoOfIso P.iso).injective (h2.trans hv.symm)
  exact congrArg Subtype.val h3
end ReciprocityTheory.AnForm.R.AffPres
