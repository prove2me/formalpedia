-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LC_Core_coreLC_of__479d7b69ca08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:49.449679+00:00
-- url     : https://prove2.me/submissions/e40a26a6-da42-49cc-87fa-a92b2e43e491

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MonomialMemSupported
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_KAlgOfAdjoinRestrict
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_kAlg_of_adjoin_restrict
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_adjoin_first_operators_preserves_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_box_finiteDimensional
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_box_le_first_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_box_mono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_compact_algebra_mul_second_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_fform_add_right
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_fform_smul_right
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_first_family_le_box
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_monomial_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Core
theorem _root_.solution (hBi : Bicomm) (hEL : EquivLift) (hRep : RepB) (hFF : FormFacts) : CoreLC := by
  intro m n ε c hc Λ hΛ p
  classical
  obtain ⟨B, hBbox, hBrep, hBcomm⟩ := hRep m n ε c hc Λ hΛ
  obtain ⟨hherm, hpos, hadj, hKbox, -⟩ := hFF m n ε c hc
  set R : Finset (Fin m → ℕ) := p.support.image (rdeg ε) with hR
  set V := box (n := n) ε (R : Set (Fin m → ℕ)) with hV
  haveI : FiniteDimensional ℂ V := box_finiteDimensional ε R
  have hKV : ∀ ij : Fin n × Fin n, ∀ f ∈ V, KopL ε ij.1 ij.2 f ∈ V := fun ij f hf => hKbox ij.1 ij.2 _ f hf
  have hBV : ∀ f ∈ V, B f ∈ V := fun f hf => hBbox _ f hf
  have hBF : ∀ f ∈ F1 ε, B f ∈ F1 ε := fun f hf => by
    have := hBbox Set.univ f (first_family_le_box ε hf)
    exact box_le_first_family ε _ this
  let T : Fin n × Fin n → Module.End ℂ V := fun ij => (KopL ε ij.1 ij.2).restrict (hKV ij)
  let x : Module.End ℂ V := B.restrict hBV
  have key : x ∈ Algebra.adjoin ℂ (Set.range T) := by
    refine hBi V (fun v w => fform c (v : PX m n) w) (fun v w₁ w₂ => by simp [fform_add_right])
      (fun v w r => by simp [fform_smul_right]) (fun v w => hherm _ _)
      (fun v hv => hpos _ (by simpa using hv)) (Fin n × Fin n) T
      (fun ij => ⟨(ij.2, ij.1), fun v w => hadj ij.1 ij.2 v w⟩) x ?_
    intro t ht
    obtain ⟨q, hq⟩ := V.exists_isCompl
    let t' : Module.End ℂ (PX m n) := V.subtype ∘ₗ t ∘ₗ V.linearProjOfIsCompl q hq
    have ht' : ∀ f (hf : f ∈ V), t' f = (t ⟨f, hf⟩ : PX m n) := fun f hf => by
      have e0 := Submodule.linearProjOfIsCompl_apply_left hq ⟨f, hf⟩
      simp only [t', LinearMap.comp_apply, Submodule.coe_subtype]
      exact congrArg (fun v => ((t v : V) : PX m n)) e0
    have h1 : ∀ f ∈ box ε (R : Set (Fin m → ℕ)), t' f ∈ box ε (R : Set (Fin m → ℕ)) := fun f hf => by
      rw [ht' f hf]; exact (t ⟨f, hf⟩).2
    have h2 : ∀ i j, ∀ f ∈ box ε (R : Set (Fin m → ℕ)), t' (KopL ε i j f) = KopL ε i j (t' f) := by
      intro i j f hf
      have e := congrArg Subtype.val (LinearMap.congr_fun (ht (i, j)) ⟨f, hf⟩)
      simp only [Module.End.mul_apply, LinearMap.restrict_apply, LinearMap.restrict_coe_apply, T] at e
      rw [ht' _ (hKV (i, j) f hf), ht' f hf]
      exact e
    obtain ⟨w, hw, hwt⟩ := hEL m n ε c hc R t' h1 h2
    obtain ⟨-, hBw⟩ := adjoin_first_operators_preserves_family ε c B hBF hBcomm w hw
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [Module.End.mul_apply, x, LinearMap.restrict_coe_apply]
    have hv1 : (t v : PX m n) = w v := by rw [← hwt v v.2, ht' v v.2]
    have hv2 : (t (B.restrict hBV v) : PX m n) = w (B v) := by
      rw [← hwt (B v) (hBV v v.2), ht' (B v) (hBV v v.2)]; rfl
    rw [hv1, hv2, hBw v (box_le_first_family ε _ v.2)]
  obtain ⟨w, hw, hwB⟩ := kAlg_of_adjoin_restrict ε V hKV x key
  refine ⟨w, hw, ?_⟩
  have hterm : ∀ s ∈ p.support, Λ (monomial s (p.coeff s)) = contr c (w (monomial s (p.coeff s))) := by
    intro s hs
    obtain ⟨e, h1, h2⟩ := monomial_split ε s (p.coeff s)
    have hsub : ({rdeg ε s} : Set (Fin m → ℕ)) ⊆ (R : Set (Fin m → ℕ)) := by
      intro r hr
      rw [Set.mem_singleton_iff] at hr
      rw [hr, hR, Finset.coe_image]
      exact Set.mem_image_of_mem _ hs
    have h1V : (monomial (s.filter (inF1 ε)) 1 : PX m n) ∈ V := box_mono ε hsub h1
    rw [e, hBrep _ (box_le_first_family ε _ h1) _ h2, compact_algebra_mul_second_family ε w hw _ _ h2]
    congr 2
    exact (hwB ⟨_, h1V⟩).symm
  have eL : Λ p = ∑ s ∈ p.support, Λ (monomial s (p.coeff s)) := by
    rw [← map_sum]; congr 1; exact p.as_sum
  have eR : contr c (w p) = ∑ s ∈ p.support, contr c (w (monomial s (p.coeff s))) := by
    show contrL c (w p) = ∑ s ∈ p.support, contrL c (w (monomial s (p.coeff s)))
    rw [← map_sum (contrL c), ← map_sum w]; congr 2; exact p.as_sum
  rw [eL, eR]
  exact Finset.sum_congr rfl hterm
end PositivityTheory.Rg.Sw.LC.Core
