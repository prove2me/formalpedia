-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_proof_847acfcecbba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:06.843846+00:00
-- url     : https://prove2.me/submissions/e45f06e5-0811-4185-9b5d-a1449c320457

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDrop
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_term_le_ddedda1072cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_interNum_fin_congr_f8923f4ce7c1

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
open Filter
universe u w
open Classical
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SectionCount.Drop
theorem _root_.solution (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb b hZ hN hb
  obtain ⟨β, hβ, hβZ, m, pp, e, c, hpp, hcount, hloss⟩ := hF k Ω N x d Nb b hZ hb
  choose c' hc' using fun j => hT k Ω N x Nb b (pp j) (e j) (c j) hN (hpp j).1
  choose C hC using fun j => hH k Ω N x Nb (pp j) (e j) hN (hpp j).1
  obtain ⟨-, hsym, -, hcut, -⟩ := hR k Ω N x
  set g : Ideal (Poly k N) → ℤ := fun qq => interNum qq (fun _ : Fin d => Nb.toSubSystem) with hg

  have hkey : ∑ j, (if e j = d then interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) else 0) =
      interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) := by
    have h1 : ∀ j, (if e j = d then interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) else 0) =
        if e j = d then g (pp j) else 0 := fun j => by
      split_ifs with h
      · exact SectionCount.Drop.interNum_fin_congr h _ _
      · rfl
    have hc4 := hcut d (primeOf (S := k) x) (fun _ => Nb) (twistBundle k x (b : ℤ)) β hZ hβ hβZ
    have htb : (twistBundle k x (b : ℤ)).toSubSystem = twistSys k x (b : ℤ) := rfl
    simp only [htb] at hc4
    have hrot := hsym (d + 1) (primeOf (S := k) x)
      (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ)) (fun _ => Nb))
      (finRotate (d + 1)) hZ
    have hL : (fun i => (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ))
        (fun _ => Nb) i).toSubSystem) = Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
          (fun _ : Fin d => Nb.toSubSystem) := by
      funext i; refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; rfl
      · simp only [Fin.cons_succ]
    have hLr : (fun i => (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ))
        (fun _ => Nb) (finRotate (d + 1) i)).toSubSystem) =
          Fin.snoc (α := fun _ => SubSystem k x Ω) (fun i : Fin d => ((fun _ => Nb) i).toSubSystem)
            (twistSys k x (b : ℤ)) := by
      funext i; refine Fin.lastCases ?_ (fun i => ?_) i
      · simp; rfl
      · simp [finRotate_apply]
    rw [← hL, ← hrot, hLr, hc4, Finset.sum_congr rfl (fun j _ => h1 j)]
    have hTq : ∀ qq : Ideal (Poly k N),
        (if h : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
            IsSubvar x qq d then
          haveI : qq.IsPrime := h.1.1.1
          ((cutMult (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β) qq).toNat : ℤ) *
            interNum qq (fun _ : Fin d => Nb.toSubSystem)
        else 0) = ∑ j, if e j = d ∧ pp j = qq then g qq else 0 := by
      intro qq
      have hq := hcount qq
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      by_cases hP : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
          IsSubvar x qq d
      · rw [dif_pos hP]; rw [dif_pos hP] at hq; rw [hq]
      · rw [dif_neg hP]; rw [dif_neg hP] at hq; rw [hq]; simp
    rw [finsum_congr hTq, finsum_eq_sum_of_support_subset (s := Finset.univ.image pp)]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hd : e j = d
      · simp only [hd, true_and, if_true]
        rw [Finset.sum_ite_eq]
        simp
      · simp [hd]
    · intro qq hqq
      rw [Function.mem_support] at hqq
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hqq
      have : pp j = qq := by
        by_contra hne; simp [hne] at hj
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨j, this⟩
  have hkeyR : ∑ j, (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0) =
      (interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) : ℝ) := by
    rw [← hkey]; push_cast; rfl
  have hev : ∀ᶠ n : ℕ in atTop, ∀ j,
      |(Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c' j) 0)
          ((twistMul Nb.toSubSystem (n + c' j) 0).twist (idealSys x (pp j))) 0) : ℝ) -
        (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) * ((n + c' j : ℕ) : ℝ) ^ (e j) /
          ((e j).factorial : ℝ)| ≤ C j * ((n + c' j : ℕ) : ℝ) ^ (e j) / ((n + c' j : ℕ) : ℝ) := by
    rw [eventually_all]; intro j
    exact (tendsto_add_atTop_nat (c' j)).eventually (hC j)
  refine ⟨∑ j, (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) *
    (1 + (c' j : ℝ)) ^ (e j), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1 i _
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h1 := (Int.cast_le (R := ℝ)).mpr (hloss n i)
  push_cast at h1
  have h3 : ∀ j, (Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c' j) 0)
      ((twistMul Nb.toSubSystem (n + c' j) 0).twist (idealSys x (pp j))) 0) : ℝ) ≤
      (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0) *
        (n : ℝ) ^ d / (d.factorial : ℝ) +
      (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) * (1 + (c' j : ℝ)) ^ (e j) *
        ((n : ℝ) ^ d / n) := fun j => by
    have hj := hn j
    push_cast at hj
    exact SectionCount.Drop.term_le _ _ _ _ _ (e j) d (hpp j).2.1 (Nat.cast_nonneg _) hn1' hj
  calc _ ≤ _ := h1
    _ ≤ _ := Finset.sum_le_sum (fun j _ => by exact_mod_cast ((hc' j) n i).2)
    _ ≤ _ := Finset.sum_le_sum (fun j _ => h3 j)
    _ = (∑ j, (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0)) *
          (n : ℝ) ^ d / (d.factorial : ℝ) +
        (∑ j, (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) *
          (1 + (c' j : ℝ)) ^ (e j)) * ((n : ℝ) ^ d / n) := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_div]
    _ = _ := by rw [hkeyR]; ring
end SectionCount.Drop
end GroundTheory.Heights₂.Heights.Kleiman
