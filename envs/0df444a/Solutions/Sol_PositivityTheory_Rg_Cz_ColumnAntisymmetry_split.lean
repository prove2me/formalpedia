-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:40:04.565289+00:00
-- url     : https://prove2.me/submissions/1b639410-52c5-4d3b-8a8e-9311cf3d1384

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (col : Fin m → ℕ) (hmono : Monotone col)
    (hc : ∀ i j : Fin m, Commute (xJ E i) (xJ E j))
    (hP : ∀ i j : Fin m, (i : ℕ) + 1 = j →
      xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 ∧
      ∀ k : Fin m, k ≠ i → k ≠ j → Commute (xJ E k) (pm (Equiv.swap i j)))
    (i j : Fin m) (hij : (i : ℕ) + 1 = j) (hcol : col i = col j) :
    ∃ R : Module.End ℂ (TV n M (Fin m)), colD E col = (xJ E i - xJ E j + 1) * R ∧
      R * pm (Equiv.swap i j) = pm (Equiv.swap i j) * R := by
  set s : Module.End ℂ (TV n M (Fin m)) := pm (Equiv.swap i j) with hs_def
  have hs2 : s * s = 1 := by rw [hs_def, ← pm_mul, Equiv.swap_mul_self, pm_one]
  obtain ⟨h1, h2⟩ := hP i j hij
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hlt : i < j := by
    rw [Fin.lt_iff_val_lt_val]
    omega
  have h3 : s * xJ E j = xJ E i * s + 1 := by
    calc s * xJ E j = s * (xJ E j * s) * s := by simp only [mul_assoc, hs2, mul_one]
      _ = s * (s * xJ E i + 1) * s := by rw [h1]
      _ = xJ E i * s + 1 := by
        rw [mul_add, add_mul, ← mul_assoc s s, hs2, one_mul, mul_one, hs2]
  have e1 : Commute (xJ E i + xJ E j) s := by
    show (xJ E i + xJ E j) * s = s * (xJ E i + xJ E j)
    rw [add_mul, mul_add, h1, h3]
    abel
  have e2 : Commute (xJ E i * xJ E j) s := by
    show xJ E i * xJ E j * s = s * (xJ E i * xJ E j)
    rw [mul_assoc, h1, (hc i j).eq, ← mul_assoc, h3]
    noncomm_ring
  have hsym : ∀ c, Commute c s → Commute c (xJ E i) →
      Commute ((xJ E i + c) * (xJ E j + c)) s := by
    intro c hcs hci
    have hexp : (xJ E i + c) * (xJ E j + c) =
        xJ E i * xJ E j + c * (xJ E i + xJ E j) + c * c := by
      rw [add_mul, mul_add, mul_add, mul_add, ← hci.eq]
      abel
    rw [hexp]
    exact (e2.add_left (hcs.mul_left e1)).add_left (hcs.mul_left hcs)
  have hsym2 : ∀ c, Commute c s → Commute c (xJ E i) →
      Commute ((c - xJ E i) * (c - xJ E j)) s := by
    intro c hcs hci
    have hh := hsym (-c) hcs.neg_left hci.neg_left
    rwa [show (c - xJ E i) * (c - xJ E j) = (xJ E i + -c) * (xJ E j + -c) by noncomm_ring]
  let S : Set (Module.End ℂ (TV n M (Fin m))) := Set.range (xJ E)
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    exact (hc k l).eq
  letI : CommRing (Algebra.adjoin ℂ S) := Algebra.adjoinCommRingOfComm ℂ hcomm
  let x' : Fin m → Algebra.adjoin ℂ S := fun k => ⟨xJ E k, Algebra.subset_adjoin ⟨k, rfl⟩⟩
  let F : Fin m → Fin m → Algebra.adjoin ℂ S := fun p q =>
    if p < q ∧ col p = col q then x' p - x' q + 1 else 1
  have hF : ∀ p q, ((F p q : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) =
      if p < q ∧ col p = col q then xJ E p - xJ E q + 1 else 1 := by
    intro p q
    simp only [F]
    split_ifs <;> rfl
  have hcoe_mul : ∀ a b : Algebra.adjoin ℂ S,
      ((a * b : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) = a * b := fun a b => rfl
  have hcoe_one : ((1 : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) = 1 := rfl
  have hlist : ∀ l : List (Algebra.adjoin ℂ S),
      ((l.prod : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) =
        (l.map Subtype.val).prod := by
    intro l
    induction l with
    | nil => exact hcoe_one
    | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, hcoe_mul, ih]
  have hcolD : colD E col = ((∏ q, ∏ p, F p q : Algebra.adjoin ℂ S) : Module.End ℂ _) := by
    simp only [← List.prod_ofFn]
    rw [hlist, List.map_ofFn]
    unfold colD
    congr 1
    congr 1
    funext q
    simp only [Function.comp_apply, hlist, List.map_ofFn, Function.comp_def]
    congr 1
    congr 1
    funext p
    exact (hF p q).symm
  have hjmem : j ∈ (Finset.univ : Finset (Fin m)).erase i :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  have hsplit : ∀ g : Fin m → Algebra.adjoin ℂ S,
      ∏ q, g q = g i * g j * ∏ q ∈ (Finset.univ.erase i).erase j, g q := by
    intro g
    rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ g hjmem, mul_assoc]
  have hmemO : ∀ p, p ∈ (Finset.univ.erase i).erase j → p ≠ i ∧ p ≠ j := by
    intro p hp
    simp only [Finset.mem_erase] at hp
    exact ⟨hp.2.1, hp.1⟩
  have Fii : F i i = 1 := by simp [F]
  have Fjj : F j j = 1 := by simp [F]
  have Fji : F j i = 1 := by
    simp only [F]
    rw [if_neg]
    rintro ⟨h, -⟩
    exact absurd (lt_trans h hlt) (lt_irrefl _)
  have hPeq : ∏ q, ∏ p, F p q = F i j *
      ((∏ p ∈ (Finset.univ.erase i).erase j, F p i * F p j) *
        (∏ q ∈ (Finset.univ.erase i).erase j, F i q * F j q) *
        ∏ q ∈ (Finset.univ.erase i).erase j, ∏ p ∈ (Finset.univ.erase i).erase j, F p q) := by
    simp only [hsplit, Fii, Fjj, Fji, one_mul, mul_one, Finset.prod_mul_distrib]
    ring
  refine ⟨(((∏ p ∈ (Finset.univ.erase i).erase j, F p i * F p j) *
        (∏ q ∈ (Finset.univ.erase i).erase j, F i q * F j q) *
        ∏ q ∈ (Finset.univ.erase i).erase j, ∏ p ∈ (Finset.univ.erase i).erase j, F p q :
          Algebra.adjoin ℂ S) : Module.End ℂ _), ?_, ?_⟩
  · rw [hcolD, hPeq, hcoe_mul, hF, if_pos ⟨hlt, hcol⟩]
  · have hmul : ∀ a b : Algebra.adjoin ℂ S,
        Commute (a : Module.End ℂ (TV n M (Fin m))) s →
        Commute (b : Module.End ℂ (TV n M (Fin m))) s →
        Commute ((a * b : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) s := by
      intro a b ha hb
      rw [hcoe_mul]
      exact ha.mul_left hb
    have hone : Commute ((1 : Algebra.adjoin ℂ S) : Module.End ℂ (TV n M (Fin m))) s := by
      rw [hcoe_one]
      exact Commute.one_left s
    have hA : Commute (((∏ p ∈ (Finset.univ.erase i).erase j, F p i * F p j :
        Algebra.adjoin ℂ S)) : Module.End ℂ (TV n M (Fin m))) s := by
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro p hp
      obtain ⟨hpi, hpj⟩ := hmemO p hp
      have hpi' : (p : ℕ) ≠ i := fun h => hpi (Fin.ext h)
      show Commute ((F p i : Module.End ℂ (TV n M (Fin m))) * (F p j : Module.End ℂ _)) s
      rw [hF, hF]
      by_cases hq : p < i ∧ col p = col i
      · rw [if_pos hq, if_pos ⟨lt_trans hq.1 hlt, hq.2.trans hcol⟩,
          show xJ E p - xJ E i + 1 = (xJ E p + 1) - xJ E i by abel,
          show xJ E p - xJ E j + 1 = (xJ E p + 1) - xJ E j by abel]
        exact hsym2 _ ((h2 p hpi hpj).add_left (Commute.one_left s))
          ((hc p i).add_left (Commute.one_left _))
      · have hn : ¬ (p < j ∧ col p = col j) := by
          rintro ⟨h, h'⟩
          apply hq
          refine ⟨?_, h'.trans hcol.symm⟩
          rw [Fin.lt_iff_val_lt_val] at h ⊢
          omega
        rw [if_neg hq, if_neg hn, mul_one]
        exact Commute.one_left s
    have hB : Commute (((∏ q ∈ (Finset.univ.erase i).erase j, F i q * F j q :
        Algebra.adjoin ℂ S)) : Module.End ℂ (TV n M (Fin m))) s := by
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro q hq
      obtain ⟨hqi, hqj⟩ := hmemO q hq
      have hqj' : (q : ℕ) ≠ j := fun h => hqj (Fin.ext h)
      show Commute ((F i q : Module.End ℂ (TV n M (Fin m))) * (F j q : Module.End ℂ _)) s
      rw [hF, hF]
      by_cases hq' : i < q ∧ col i = col q
      · have hjq : j < q := by
          have := hq'.1
          rw [Fin.lt_iff_val_lt_val] at this ⊢
          omega
        rw [if_pos hq', if_pos ⟨hjq, hcol.symm.trans hq'.2⟩,
          show xJ E i - xJ E q + 1 = xJ E i + (1 - xJ E q) by abel,
          show xJ E j - xJ E q + 1 = xJ E j + (1 - xJ E q) by abel]
        exact hsym _ ((Commute.one_left s).sub_left (h2 q hqi hqj))
          ((Commute.one_left _).sub_left (hc q i))
      · have hn : ¬ (j < q ∧ col j = col q) := by
          rintro ⟨h, h'⟩
          apply hq'
          refine ⟨?_, hcol.trans h'⟩
          rw [Fin.lt_iff_val_lt_val] at h ⊢
          omega
        rw [if_neg hq', if_neg hn, mul_one]
        exact Commute.one_left s
    have hC : Commute (((∏ q ∈ (Finset.univ.erase i).erase j,
        ∏ p ∈ (Finset.univ.erase i).erase j, F p q :
        Algebra.adjoin ℂ S)) : Module.End ℂ (TV n M (Fin m))) s := by
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro q hq
      refine Finset.prod_induction _ (fun b : Algebra.adjoin ℂ S =>
        Commute (b : Module.End ℂ (TV n M (Fin m))) s) hmul hone ?_
      intro p hp
      obtain ⟨hqi, hqj⟩ := hmemO q hq
      obtain ⟨hpi, hpj⟩ := hmemO p hp
      show Commute (F p q : Module.End ℂ (TV n M (Fin m))) s
      rw [hF]
      split_ifs
      · exact ((h2 p hpi hpj).sub_left (h2 q hqi hqj)).add_left (Commute.one_left s)
      · exact Commute.one_left s
    exact (hmul _ _ (hmul _ _ hA hB) hC).eq
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
