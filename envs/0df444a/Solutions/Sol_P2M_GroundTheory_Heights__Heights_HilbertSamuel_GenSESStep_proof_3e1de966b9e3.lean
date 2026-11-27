-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_proof_3e1de966b9e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:03:52.842904+00:00
-- url     : https://prove2.me/submissions/6d8a1d48-df34-4d10-8f6a-8547bf59e5e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_mul_0a86f7155eda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_cellMon_homog_9faa70fa300d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mk_mem_locPart_8ee0fd2ff896
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_locPart_normal_f08e45df3bf5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_smul_mem_locPart_91dd9ddd0d34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_locMap_mk_f994272c12bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mem_of_map_mem_344b3ce95714

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
theorem _root_.solution (hSES : KH.CechSESStatement) (hMap : KH.CechMapDegStatement) : GenSESStep.Statement := by
  intro S _ K _ _ ι _ _ M' _ _ _ _ M _ _ _ _ M'' _ _ _ _ 𝓜' 𝓜 𝓜'' g h h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex d
    hH1 hgen' hgen'' I x hx

  obtain ⟨m₀, t₀, a₀, ht₀, hm₀, rfl⟩ := locPart_normal h𝓜 hx
  have hx'' : LocalizedModule.mk (h m₀) t₀ ∈ KH.locPart ι 𝓜'' (KH.cellMon S I.1) d :=
    mk_mem_locPart _ _ a₀ ht₀ (hh _ _ hm₀)
  obtain ⟨t₁, a₁, r, p, z'', ht₁T, ht₁, hp, hz'', e₁⟩ := hgen'' I _ hx''

  have hlift := fun j => (hSES S K ι M' M M'' 𝓜' 𝓜 𝓜'' g h h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex d
    0).2.2.2.2.1 hH1 (z'' j) (hz'' j)
  choose z hz hzmap using hlift
  have hzI : ∀ j, z j I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d :=
    fun j => Submodule.mem_pi.mp (hz j).1 I (Set.mem_univ _)
  have hzh : ∀ j, locMap (KH.cellMon S I.1) h (z j I) = z'' j I := fun j => congrFun (hzmap j) I

  obtain ⟨y, hy_def⟩ : ∃ y, y = t₁ • LocalizedModule.mk m₀ t₀ - ∑ j, p j • z j I := ⟨_, rfl⟩
  have hLy : locMap (KH.cellMon S I.1) h y = 0 := by
    rw [hy_def, map_sub, map_smul, map_sum, locMap_mk, e₁, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hzh]
  have hyloc : y ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) (d + fun k => (a₁ k : ℤ)) := by
    rw [hy_def]
    exact sub_mem (smul_mem_locPart h𝓜 ht₁ hx)
      (Submodule.sum_mem _ fun j _ => smul_mem_locPart h𝓜 (hp j) (hzI j))
  obtain ⟨m, s, b, hs, hm, hys⟩ := locPart_normal h𝓜 hyloc

  have h0 : LocalizedModule.mk (h m) s = 0 := by rw [← locMap_mk, ← hys]; exact hLy
  rw [← LocalizedModule.zero_mk (1 : KH.cellMon S I.1), LocalizedModule.mk_eq] at h0
  obtain ⟨u, hu⟩ := h0
  rw [one_smul, smul_zero, smul_zero] at hu
  have hker : u • m ∈ LinearMap.ker h := by
    rw [LinearMap.mem_ker, Submonoid.smul_def, map_smul, ← Submonoid.smul_def]
    exact hu
  rw [← hex] at hker
  obtain ⟨m', hm'⟩ := hker
  obtain ⟨e, hue⟩ := cellMon_homog u.2
  have hm'deg : m' ∈ 𝓜' (((d + fun k => (a₁ k : ℤ)) + fun k => (b k : ℤ)) + fun k => (e k : ℤ)) := by
    refine mem_of_map_mem h𝓜' h𝓜 hg hinj ?_
    rw [hm', Submonoid.smul_def]
    exact h𝓜.2 _ _ _ _ hue hm

  let v : KH.cellMon S I.1 := ⟨t₁, ht₁T⟩ * u * s
  have hv : IsMultiHomog (v : MRingOver S ι) (a₁ + e + b) := isMultiHomog_mul (isMultiHomog_mul ht₁ hue) hs
  have hy'' : LocalizedModule.mk m' v ∈ KH.locPart ι 𝓜' (KH.cellMon S I.1) d := by
    refine mk_mem_locPart _ v _ hv ?_
    have edeg : (d + fun k => ((a₁ + e + b) k : ℤ)) =
        ((d + fun k => (a₁ k : ℤ)) + fun k => (b k : ℤ)) + fun k => (e k : ℤ) := by
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    rw [edeg]
    exact hm'deg
  obtain ⟨t₂, a₂, r', p', z', ht₂T, ht₂, hp', hz', e₂⟩ := hgen' I _ hy''

  have hw : ∀ l, KH.cechMap S ι g 0 (z' l) ∈ KH.cechZc ι 𝓜 d 0 := by
    intro l
    obtain ⟨h1, h2⟩ := hMap S K ι M' M 𝓜' 𝓜 g d 0 hg
    refine ⟨h1 _ (hz' l).1, LinearMap.mem_ker.mpr ?_⟩
    rw [← LinearMap.comp_apply, h2, LinearMap.comp_apply, LinearMap.mem_ker.mp (hz' l).2, map_zero]
  have hgv : (t₁ : MRingOver S ι) • locMap (KH.cellMon S I.1) g (LocalizedModule.mk m' v) = y := by
    rw [locMap_mk, LocalizedModule.smul'_mk, hm', hys]
    have : (t₁ : MRingOver S ι) • (u • m) = ((⟨t₁, ht₁T⟩ * u : KH.cellMon S I.1) • m) := by
      rw [Submonoid.smul_def, Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    rw [this]
    exact LocalizedModule.mk_cancel_common_left _ _ _
  have hgy : t₂ • y = t₁ • ∑ l, p' l • KH.cechMap S ι g 0 (z' l) I := by
    rw [← hgv, ← mul_smul, mul_comm, mul_smul, ← map_smul, e₂, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
    rw [map_smul]
    rfl
  refine ⟨t₂ * t₁, a₂ + a₁, r + r', Fin.append (fun j => t₂ * p j) (fun l => t₁ * p' l),
    Fin.append z (fun l => KH.cechMap S ι g 0 (z' l)), mul_mem ht₂T ht₁T, isMultiHomog_mul ht₂ ht₁,
    fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun l => ?_) j
    · rw [Fin.append_left]
      exact isMultiHomog_mul ht₂ (hp j)
    · rw [Fin.append_right, add_comm]
      exact isMultiHomog_mul ht₁ (hp' l)
  · refine Fin.addCases (fun j => ?_) (fun l => ?_) j
    · rw [Fin.append_left]
      exact hz j
    · rw [Fin.append_right]
      exact hw l
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have hyeq : t₁ • LocalizedModule.mk m₀ t₀ = y + ∑ j, p j • z j I := by
      rw [hy_def, sub_add_cancel]
    rw [mul_smul, hyeq, smul_add, hgy, Finset.smul_sum, Finset.smul_sum, add_comm]
    simp only [smul_smul]
end GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
