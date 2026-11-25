-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.Sys.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:33.798996+00:00
-- url     : https://prove2.me/submissions/a0914139-bc77-4926-96af-5beb3d36c176

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen
import Theorems.Thm_PositivityTheory_ThKG_Fub_Split_fub
import Theorems.Thm_PositivityTheory_ThKG_Fub_exists_haar
import Theorems.Thm_PositivityTheory_ThKG_Fub_Sys_closed
import Theorems.Thm_PositivityTheory_ThKG_Fub_Sys_split
import Theorems.Thm_PositivityTheory_ThKG_Fub_Sys_good_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
open scoped NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {S A B : Subgroup G} {p q : G →* G}
variable {R : Type} [CommRing R]
variable {P : R → G →* G} {K : Subgroup G} {U : Set G} {good : R → Prop}
namespace PositivityTheory.ThKG.Fub
namespace Sys
theorem _root_.solution (s : Sys P K U good) {ι : Type} [DecidableEq ι] (e : ι → R) (he : ∀ i, good (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) (c : R) (hc : good c) (α : ∀ i, Measure (part P K (e i)))
    (hα : ∀ i, (α i).IsHaarMeasure ∧ α i {x | x.1 ∈ U} = 1) (β : Measure (part P K c))
    (hβ : β.IsHaarMeasure ∧ β {x | x.1 ∈ U} = 1) (T : Finset ι) (hT : ∀ i ∈ T, e i * c = 0)
    (hCO : ∀ T' ⊆ T, CO P K U (∑ i ∈ T', e i + c)) (b : R) (hb : b = ∑ i ∈ T, e i + c)
    (μ : Measure (part P K b)) (hμ : μ.IsHaarMeasure ∧ μ {x | x.1 ∈ U} = 1) (f : ι → G → ℂ) (g : G → ℂ)
    (hf : ∀ i ∈ T, Integrable (fun x : part P K (e i) => f i x) (α i)) (hg : Integrable (fun x : part P K c => g x) β) :
    Integrable (fun x : part P K b => (∏ i ∈ T, f i (P (e i) x)) * g (P c x)) μ ∧
      ∫ x : part P K b, (∏ i ∈ T, f i (P (e i) x)) * g (P c x) ∂μ =
        (∏ i ∈ T, ∫ x : part P K (e i), f i x ∂(α i)) * ∫ x : part P K c, g x ∂β := by
  induction T using Finset.induction_on generalizing b with
  | empty =>
    obtain rfl : b = c := by simpa using hb
    haveI := hμ.1; haveI := hβ.1
    haveI : LocallyCompactSpace (part P K b) := (s.closed hc).locallyCompactSpace
    have h1 := Measure.isMulLeftInvariant_eq_smul μ β
    have h2 : Measure.haarScalarFactor μ β = 1 := by
      have := hμ.2
      rw [h1, Measure.smul_apply, hβ.2] at this
      simpa using this
    rw [h2, one_smul] at h1
    have h3 : (fun x : part P K b => (∏ i ∈ (∅ : Finset ι), f i (P (e i) x)) * g (P b x)) = fun x : part P K b => g x := by
      funext x; rw [show P b x = x from x.2.2]; simp
    rw [h3, h1]; exact ⟨hg, by simp⟩
  | insert i T hi ih =>
    have hT' : ∀ j ∈ T, e j * c = 0 := fun j hj => hT j (Finset.mem_insert_of_mem hj)
    have hg' := s.good_sum e he ho c hc T hT'
    set b' := ∑ j ∈ T, e j + c with hb'
    have h0 : e i * b' = 0 := by
      rw [hb', mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => ho i j (fun e => hi (e ▸ hj)),
        hT i (Finset.mem_insert_self _ _), add_zero]
    obtain rfl : b = e i + b' := by rw [hb, Finset.sum_insert hi, add_assoc]
    obtain ⟨μ', hμ'⟩ := exists_haar _ (s.closed hg') U s.one (hCO T (Finset.subset_insert _ _)).1 (hCO T (Finset.subset_insert _ _)).2
    obtain ⟨i1, i2⟩ := ih hT' (fun T' h => hCO T' (h.trans (Finset.subset_insert _ _))) b' rfl μ' hμ'
      (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    haveI := hμ.1; haveI := hμ'.1; haveI := (hα i).1
    obtain ⟨k, -, k1, k2⟩ := (s.split (he i) hg' h0).fub μ (α i) μ'
    have hk : k = 1 := by
      have := k2 U s.mU fun x hx => ⟨fun h => ⟨s.pU _ (he i) _ h, s.pU _ hg' _ h⟩, fun h => by
        rw [← (s.split (he i) hg' h0).mul x hx]; exact s.mul _ h.1 _ h.2⟩
      rw [hμ.2, (hα i).2, hμ'.2] at this
      simpa using this.symm
    obtain ⟨j1, j2⟩ := k1 (f i) (fun y => (∏ j ∈ T, f j (P (e j) y)) * g (P c y)) (hf i (Finset.mem_insert_self _ _)) i1
    have h3 : (fun x : part P K (e i + b') => (∏ j ∈ insert i T, f j (P (e j) x)) * g (P c x)) =
        fun x : part P K (e i + b') => f i (P (e i) x) * ((∏ j ∈ T, f j (P (e j) (P b' x))) * g (P c (P b' x))) := by
      funext x
      rw [Finset.prod_insert hi, mul_assoc, s.comp c b' hc hg']
      have e1 : c * b' = c := by
        rw [hb', mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => by rw [mul_comm]; exact hT' j hj, zero_add, s.idem c hc]
      rw [e1]
      congr 2
      refine Finset.prod_congr rfl fun j hj => ?_
      have e2 : e j * b' = e j := by
        rw [hb', mul_add, hT' j hj, add_zero, Finset.mul_sum,
          Finset.sum_eq_single_of_mem j hj fun l _ hl => ho j l hl.symm, s.idem _ (he j)]
      rw [s.comp _ b' (he j) hg', e2]
    rw [h3]
    refine ⟨j1, ?_⟩
    rw [j2, i2, hk, Finset.prod_insert hi]; simp [mul_assoc]
end Sys
end PositivityTheory.ThKG.Fub
