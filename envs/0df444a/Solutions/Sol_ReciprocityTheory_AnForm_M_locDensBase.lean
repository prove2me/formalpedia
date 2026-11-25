-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDensBase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:38:42.878609+00:00
-- url     : https://prove2.me/submissions/ab118f51-14e8-4d24-9261-b4feb79b611d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessCGerm
import Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_congr_hessC
import Theorems.Thm_ReciprocityTheory_AnForm_M_potSmoothAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_add_re_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : LocDensBaseStatement := by
  intro e X _ A Φ hΦ j y hy x hx
  unfold locDens
  apply maDens_congr_hessC
  intro i
  obtain ⟨W, hW, hpW, G, hG, hGeq⟩ :=
    (hΦ i).2 ((A.chart j).symm y) (x i) ((A.chart j).symm y) ⟨(Φ i).mem_U _, hx i⟩

  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x i))) :=
    (A.chart j).isOpen_inter_preimage_symm
      ((hW.inter ((Φ i).isOpen_U _)).inter ((Φ i).isOpen_U (x i)))
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x i)) :=
    ⟨hy, ⟨⟨hpW, (Φ i).mem_U _⟩, hx i⟩⟩
  have hev : (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[nhds y]
      (fun y' => (Φ i).φ (x i) ((A.chart j).symm y') + (G ((A.chart j).symm y')).re) := by
    filter_upwards [hopen.mem_nhds hmem] with y' hy'
    rw [← hGeq _ hy'.2]
    ring
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hpW⟩
  have hφs : ContDiffAt ℝ 2 ((Φ i).φ (x i) ∘ (A.chart j).symm) y :=
    potSmoothAt A (Φ i) (hΦ i) (x i) j ⟨hy, hx i⟩
  exact (hessCGerm _ _ y hev).trans (ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ (G ∘ (A.chart j).symm) y hφs hGa)
end ReciprocityTheory.AnForm.M
