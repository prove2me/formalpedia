-- Prove2me | solution 1 for SubadditiveMMS580.Amplification.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:20:38.616189+00:00
-- url     : https://prove2.me/submissions/80bee4b3-d12e-409f-be85-59c94c154a56

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting
import Theorems.Thm_SubadditiveMMS580_Amplification_proposition_3_4
import Theorems.Thm_MultiAllocToAlloc_Subadditive_theorem_1

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.P34

variable {n m : ℕ}

/-- Index of the `a`-th member of `U`. -/
noncomputable def sig (U : Finset (Fin n)) (a : Fin U.card) : Fin n := ((U.equivFin.symm a : U) : Fin n)

theorem sig_mem (U : Finset (Fin n)) (a : Fin U.card) : sig U a ∈ U :=
  (U.equivFin.symm a).2

theorem transfer (U : Finset (Fin n)) (A : Fin U.card → Finset (Fin m))
    (hA : IsAllocation A) :
    ∃ C : Fin n → Finset (Fin m), IsAllocation C ∧ ∀ a, C (sig U a) = A a := by
  classical
  refine ⟨fun i => if h : i ∈ U then A (U.equivFin ⟨i, h⟩) else ∅, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i ∈ U <;> by_cases hj : j ∈ U
    · simp only [hi, hj, dif_pos]
      apply hA
      intro h
      exact hij (by simpa using congrArg Subtype.val (U.equivFin.injective h))
    · simp [hj]
    · simp [hi]
    · simp [hi]
  · intro a
    have h := sig_mem U a
    simp only [h, dif_pos]
    congr 1
    have : (⟨sig U a, h⟩ : U) = U.equivFin.symm a := rfl
    rw [this]; simp

end SubadditiveMMS580.Amplification.Dev.P34
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.P34

variable {n m : ℕ}

end SubadditiveMMS580.Amplification.Dev.P34
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.P34

variable {n m : ℕ}

theorem le_tower_logStar (n : ℕ) : n ≤ tower (logStar n) :=
  Nat.find_spec (⟨n, le_tower_self n⟩ : ∃ r, n ≤ tower r)

variable (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) (hn : 1 ≤ n)
    (W : Fin n → Fin n → Finset (Fin m))
    (hW : ∀ i, SubadditiveMMS580.Amplification.IsValuableFamily (v i) (W i))

include hnorm hmono hsub hn hW

end SubadditiveMMS580.Amplification.Dev.P34
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.T11

theorem mms_le_of_merge {m : ℕ} (w : Finset (Fin m) → ℝ) (hmono : IsMonotone w) (k : ℕ)
    (hk : 1 ≤ k) (S S' : Finset (Fin m))
    (h : ∀ f : Fin m → Fin (k + 1), ∃ c, ∀ x ∈ S, x ∉ S' → f x = c) :
    LittleCharity.MMS.mms w (k + 1) S ≤ LittleCharity.MMS.mms w k S' := by
  classical
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : Nonempty (Fin (k + 1)) := ⟨0⟩
  unfold LittleCharity.MMS.mms
  apply ciSup_le
  intro f
  obtain ⟨c, hc⟩ := h f
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin (k + 1) → Fin k, ∀ j, φ (c.succAbove j) = j :=
    (Fin.succAbove_right_injective (p := c)).hasLeftInverse
  refine le_trans ?_ (le_ciSup (f := fun f' : Fin m → Fin k =>
    ⨅ j : Fin k, w (S'.filter (fun x => f' x = j)))
    (Set.finite_range _).bddAbove (fun x => φ (f x)))
  apply le_ciInf
  intro j'
  refine le_trans (ciInf_le (Set.finite_range _).bddBelow (c.succAbove j')) ?_
  apply hmono
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  obtain ⟨hxS, hxf⟩ := hx
  have hxS' : x ∈ S' := by
    by_contra hxn
    have := hc x hxS hxn
    exact Fin.succAbove_ne c j' (by rw [← hxf, this])
  exact ⟨hxS', by rw [hxf, hφ]⟩

theorem mms_le_remove {m : ℕ} (w : Finset (Fin m) → ℝ) (hmono : IsMonotone w) (k : ℕ)
    (hk : 1 ≤ k) (S X : Finset (Fin m)) (hX : X.card ≤ 1) :
    LittleCharity.MMS.mms w (k + 1) S ≤ LittleCharity.MMS.mms w k (S \ X) := by
  refine mms_le_of_merge w hmono k hk S (S \ X) (fun f => ?_)
  rcases X.eq_empty_or_nonempty with rfl | ⟨g, hg⟩
  · exact ⟨0, fun x hx hx' => absurd (by simpa using hx) hx'⟩
  · refine ⟨f g, fun x hx hx' => ?_⟩
    have : x ∈ X := by
      by_contra hxX
      exact hx' (Finset.mem_sdiff.2 ⟨hx, hxX⟩)
    rw [Finset.card_le_one.1 hX x this g hg]

theorem mms_nonneg {m : ℕ} (w : Finset (Fin m) → ℝ) (hnorm : IsNormalized w)
    (hmono : IsMonotone w) (k : ℕ) (S : Finset (Fin m)) :
    0 ≤ LittleCharity.MMS.mms w k S := by
  have hw : ∀ T, 0 ≤ w T := fun T => by
    have := hmono ∅ T (Finset.empty_subset _)
    rwa [hnorm] at this
  unfold LittleCharity.MMS.mms
  exact Real.iSup_nonneg (fun f => Real.iInf_nonneg (fun j => hw _))

theorem mms_one {m : ℕ} (w : Finset (Fin m) → ℝ) (S : Finset (Fin m)) :
    LittleCharity.MMS.mms w 1 S = w S := by
  classical
  unfold LittleCharity.MMS.mms
  have : ∀ f : Fin m → Fin 1, (⨅ j : Fin 1, w (S.filter (fun g => f g = j))) = w S := by
    intro f
    rw [ciInf_unique]
    congr 1
    apply Finset.filter_true_of_mem
    intro x _
    exact Subsingleton.elim _ _
  simp_rw [this]
  exact ciSup_const

theorem exists_partition {m : ℕ} (w : Finset (Fin m) → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (S : Finset (Fin m)) :
    ∃ f : Fin m → Fin k, LittleCharity.MMS.mms w k S =
      ⨅ j : Fin k, w (S.filter (fun g => f g = j)) := by
  classical
  have : Nonempty (Fin m → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  unfold LittleCharity.MMS.mms
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := fun f : Fin m → Fin k =>
    ⨅ j : Fin k, w (S.filter (fun g => f g = j)))
  exact ⟨f, hf.symm⟩

end SubadditiveMMS580.Amplification.Dev.T11
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.T11

open SubadditiveMMS580.Amplification.Dev.P34

variable {n m : ℕ}

theorem logStar_mono {a b : ℕ} (h : a ≤ b) : logStar a ≤ logStar b :=
  Nat.find_min' _ (le_trans h (le_tower_logStar b))

theorem logStar_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ logStar n := by
  by_contra hk
  have h0 : logStar n = 0 := by omega
  have := le_tower_logStar n
  rw [h0] at this
  simp [tower] at this
  omega

theorem alpha_facts (n : ℕ) (hn : 2 ≤ n) :
    0 < alpha n ∧ alpha n ≤ 1 ∧ alpha n * (4 * (bigD n : ℝ) - 2) = 1 ∧ 2 ≤ bigD n ∧
      1 + logStar n ≤ bigD n ∧ ∃ k, 1 ≤ k ∧ bigD n = 2 ^ k := by
  have h1 := logStar_pos hn
  have hd : 2 ≤ dFun n := by unfold dFun; omega
  have hk : 0 < Nat.clog 2 (dFun n) := Nat.clog_pos (by norm_num) hd
  have hD2 : 2 ≤ bigD n := by
    unfold bigD
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Nat.clog 2 (dFun n) := Nat.pow_le_pow_right (by norm_num) hk
  have hDd : dFun n ≤ bigD n := Nat.le_pow_clog (by norm_num) _
  have hD : (2 : ℝ) ≤ (bigD n : ℝ) := by exact_mod_cast hD2
  have hpos : (0 : ℝ) < 4 * (bigD n : ℝ) - 2 := by linarith
  refine ⟨?_, ?_, ?_, hD2, ?_, ⟨Nat.clog 2 (dFun n), hk, rfl⟩⟩
  · unfold alpha; positivity
  · unfold alpha; rw [div_le_one hpos]; linarith
  · unfold alpha; field_simp
  · unfold dFun at hDd; exact hDd

theorem main_reduction (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) (hn2 : 2 ≤ n)
    (β : Fin n → ℝ) (hβ0 : ∀ i, 0 ≤ β i) :
    ∀ c : ℕ, ∀ I : Finset (Fin n), I.card = c → 1 ≤ c → ∀ S : Finset (Fin m),
      (∀ i ∈ I, β i ≤ LittleCharity.MMS.mms (v i) c S) →
      ∃ A : Fin n → Finset (Fin m), (∀ i ∈ I, A i ⊆ S) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)) ∧
        ∀ i ∈ I, alpha n * β i ≤ v i (A i) := by
  classical
  obtain ⟨hα0, hα1, hαD, hD2, hDd, hDk⟩ := alpha_facts n hn2
  have hv0 : ∀ i T, 0 ≤ v i T := fun i T => by
    have := hmono i ∅ T (Finset.empty_subset _)
    rwa [hnorm i] at this
  intro c
  induction c with
  | zero => intro I hI hc; omega
  | succ c ih =>
    intro I hI _ S hmms
    by_cases hc0 : c = 0
    · -- one agent
      subst hc0
      obtain ⟨i0, rfl⟩ := Finset.card_eq_one.1 hI
      refine ⟨fun _ => S, by simp, by simp, ?_⟩
      intro i hi
      rw [Finset.mem_singleton] at hi
      subst hi
      have h1 := hmms i (Finset.mem_singleton_self _)
      rw [mms_one] at h1
      nlinarith [hβ0 i]
    have hc1 : 1 ≤ c := by omega
    by_cases hred : ∃ i ∈ I, ∃ X ⊆ S, X.card ≤ 1 ∧ alpha n * β i ≤ v i X
    · obtain ⟨i, hi, X, hXS, hX, hval⟩ := hred
      have hcard : (I.erase i).card = c := by rw [Finset.card_erase_of_mem hi, hI]; rfl
      obtain ⟨A, hAS, hAd, hAv⟩ := ih (I.erase i) hcard hc1 (S \ X) (by
        intro j hj
        exact le_trans (hmms j (Finset.mem_of_mem_erase hj))
          (mms_le_remove (v j) (hmono j) c hc1 S X hX))
      refine ⟨fun j => if j = i then X else A j, ?_, ?_, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · simp [hji, hXS]
        · simp only [hji, if_false]
          exact (hAS j (Finset.mem_erase.2 ⟨hji, hj⟩)).trans Finset.sdiff_subset
      · intro j hj k hk hjk
        by_cases hji : j = i <;> by_cases hki : k = i
        · exact absurd (hji.trans hki.symm) hjk
        · simp only [hji, hki, if_true, if_false]
          exact Finset.disjoint_of_subset_right (hAS k (Finset.mem_erase.2 ⟨hki, hk⟩))
            Finset.disjoint_sdiff
        · simp only [hji, hki, if_true, if_false]
          exact (Finset.disjoint_of_subset_right (hAS j (Finset.mem_erase.2 ⟨hji, hj⟩))
            Finset.disjoint_sdiff).symm
        · simp only [hji, hki, if_false]
          exact hAd j (Finset.mem_erase.2 ⟨hji, hj⟩) k (Finset.mem_erase.2 ⟨hki, hk⟩) hjk
      · intro j hj
        by_cases hji : j = i
        · subst hji; simpa using hval
        · simp only [hji, if_false]
          exact hAv j (Finset.mem_erase.2 ⟨hji, hj⟩)
    · push Not at hred
      -- the working instance
      have hno : ∀ i ∈ I, ∀ X ⊆ S, X.card ≤ 1 → v i X < alpha n * β i :=
        fun i hi X hX hc => hred i hi X hX hc
      have hβpos : ∀ i ∈ I, 0 < β i := by
        intro i hi
        have := hno i hi ∅ (Finset.empty_subset _) (by simp)
        rw [hnorm i] at this
        exact pos_of_mul_pos_right this hα0.le |> fun h => by
          by_contra hh; push Not at hh; nlinarith
      have hmms' : ∀ i ∈ I, β i ≤ LittleCharity.MMS.mms (v i) I.card S := by
        intro i hi; rw [hI]; exact hmms i hi
      have ht2 : 2 ≤ I.card := by omega
      have htn : I.card ≤ n := by simpa using Finset.card_le_univ I
      set t := I.card with ht
      choose f hf using fun a : Fin t => exists_partition (v (sig I a)) t (by omega) S
      have hpart : ∀ a r, β (sig I a) ≤ v (sig I a) (S.filter (fun g => f a g = r)) := by
        intro a r
        refine le_trans (hmms' _ (sig_mem I a)) ?_
        rw [hf a]
        exact ciInf_le (Set.finite_range _).bddBelow r
      let x : Fin t → Finset (Fin m) → ℝ := fun a T => v (sig I a) (T ∩ S) / β (sig I a)
      have hβa : ∀ a, 0 < β (sig I a) := fun a => hβpos _ (sig_mem I a)
      have hxnorm : ∀ a, IsNormalized (x a) := by
        intro a
        show v (sig I a) (∅ ∩ S) / β (sig I a) = 0
        rw [Finset.empty_inter, hnorm, zero_div]
      have hxmono : ∀ a, IsMonotone (x a) := by
        intro a T T' h
        exact div_le_div_of_nonneg_right (hmono _ _ _ (Finset.inter_subset_inter_right h))
          (hβa a).le
      have hxsub : ∀ a, SubmodOrder.Subadditive (x a) := by
        intro a T T'
        show v _ ((T ∪ T') ∩ S) / _ ≤ v _ (T ∩ S) / _ + v _ (T' ∩ S) / _
        rw [← add_div, Finset.union_inter_distrib_right]
        exact div_le_div_of_nonneg_right (hsub _ _ _) (hβa a).le
      let W : Fin t → Fin t → Finset (Fin m) := fun a r => S.filter (fun g => f a g = r)
      have hW : ∀ a, IsValuableFamily (x a) (W a) := by
        intro a
        refine ⟨?_, ?_⟩
        · intro r s hrs
          exact Finset.disjoint_filter.2 (fun y _ h1 h2 => hrs (h1.symm.trans h2))
        · intro r
          show 1 ≤ v _ (S.filter (fun g => f a g = r) ∩ S) / β (sig I a)
          rw [Finset.inter_eq_left.2 (Finset.filter_subset _ _), le_div_iff₀ (hβa a)]
          simpa using hpart a r
      obtain ⟨B, hB, hBv⟩ := proposition_3_4 t ht2 x hxnorm hxmono hxsub W hW
      let B' : Fin t → Finset (Fin m) := fun a => B a ∩ S
      have hB' : IsMultiAllocation (bigD n) B' := by
        intro e
        refine le_trans (Finset.card_le_card ?_) (le_trans (hB e) ?_)
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, B'] at ha ⊢
          exact (Finset.mem_inter.1 ha).1
        · have := logStar_mono htn
          omega
      have hxB' : ∀ a, x a (B' a) = x a (B a) := by
        intro a
        show v _ ((B a ∩ S) ∩ S) / _ = v _ (B a ∩ S) / _
        rw [Finset.inter_assoc, Finset.inter_self]
      obtain ⟨A', hA', hsubB, hA'v⟩ := theorem_1 (n := t) (bigD n) hDk B' hB' x hxnorm hxmono hxsub
      have hδ : ∀ a, maxItemValue (x a) (B' a) ≤ alpha n := by
        intro a
        unfold maxItemValue
        split_ifs with hne
        · apply Finset.sup'_le
          intro e he
          have heS : e ∈ S := (Finset.mem_inter.1 he).2
          show v _ ({e} ∩ S) / _ ≤ _
          rw [Finset.inter_eq_left.2 (Finset.singleton_subset_iff.2 heS), div_le_iff₀ (hβa a)]
          exact (hno _ (sig_mem I a) {e} (Finset.singleton_subset_iff.2 heS) (by simp)).le
        · exact hα0.le
      have hDR : (2 : ℝ) ≤ (bigD n : ℝ) := by exact_mod_cast hD2
      have hAval : ∀ a, alpha n ≤ x a (A' a) := by
        intro a
        have h1 := hA'v a
        have h2 := hBv a
        rw [← hxB'] at h2
        have hδa := hδ a
        have hD0 : (0 : ℝ) < bigD n := by linarith
        have hkey : (1 / 2 : ℝ) / (bigD n : ℝ) - ((bigD n : ℝ) - 1) / (bigD n : ℝ) * alpha n
            = alpha n := by
          field_simp
          nlinarith [hαD]
        refine le_trans ?_ h1
        rw [← hkey]
        have h3 : (1 / 2 : ℝ) / (bigD n : ℝ) ≤ x a (B' a) / (bigD n : ℝ) :=
          div_le_div_of_nonneg_right h2 hD0.le
        have h4 : ((bigD n : ℝ) - 1) / (bigD n : ℝ) * maxItemValue (x a) (B' a) ≤
            ((bigD n : ℝ) - 1) / (bigD n : ℝ) * alpha n :=
          mul_le_mul_of_nonneg_left hδa (div_nonneg (by linarith) hD0.le)
        linarith
      obtain ⟨C, hC, hCa⟩ := transfer I A' hA'
      refine ⟨C, ?_, fun i _ j _ hij => hC i j hij, ?_⟩
      · intro i hi
        have hia : sig I (I.equivFin ⟨i, hi⟩) = i := by simp [sig]
        rw [← hia, hCa]
        exact (hsubB _).trans (Finset.inter_subset_right)
      · intro i hi
        have hia : sig I (I.equivFin ⟨i, hi⟩) = i := by simp [sig]
        set a := I.equivFin ⟨i, hi⟩ with ha
        have h1 := hAval a
        have hsubS : A' a ⊆ S := (hsubB a).trans Finset.inter_subset_right
        have h2 : x a (A' a) = v (sig I a) (A' a) / β (sig I a) := by
          show v _ (A' a ∩ S) / _ = _
          rw [Finset.inter_eq_left.2 hsubS]
        rw [h2, le_div_iff₀ (hβa a)] at h1
        have e : C i = A' a := by
          have := hCa a
          rwa [hia] at this
        rw [e]
        rw [hia] at h1
        linarith

end SubadditiveMMS580.Amplification.Dev.T11
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification
open SubadditiveMMS580.Amplification.Dev.T11 in
theorem chk_theorem_1_1 (n : ℕ) (hn : 2 ≤ n) {m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) :
    (∃ A : Fin n → Finset (Fin m), IsAllocation A ∧
      ∀ i : Fin n, alpha n * LittleCharity.MMS.mms (v i) n Finset.univ ≤ v i (A i)) ∧
    1 / (8 * (1 + (logStar n : ℝ))) < alpha n := by
  obtain ⟨hα0, hα1, hαD, hD2, hDd, hDk⟩ := alpha_facts n hn
  refine ⟨?_, ?_⟩
  · obtain ⟨A, -, hAd, hAv⟩ := main_reduction v hnorm hmono hsub hn
      (fun i => LittleCharity.MMS.mms (v i) n Finset.univ)
      (fun i => mms_nonneg _ (hnorm i) (hmono i) _ _) n Finset.univ (by simp) (by omega)
      Finset.univ (fun i _ => le_rfl)
    exact ⟨A, fun i j hij => hAd i (Finset.mem_univ _) j (Finset.mem_univ _) hij,
      fun i => hAv i (Finset.mem_univ _)⟩
  · -- 1/(8 d) < α(n) = 1/(4D-2), with D < 2 d
    have hlt : bigD n < 2 * dFun n := by
      unfold bigD
      have hd : 2 ≤ dFun n := by unfold dFun; have := logStar_pos hn; omega
      have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < dFun n by omega)
      simp only [Nat.pred_eq_sub_one] at this
      have hk := Nat.clog_pos (b := 2) (by norm_num) hd
      calc 2 ^ Nat.clog 2 (dFun n) = 2 * 2 ^ (Nat.clog 2 (dFun n) - 1) := by
            rw [← pow_succ']; congr 1; omega
        _ < 2 * dFun n := by omega
    have hltR : (bigD n : ℝ) + 1 ≤ 2 * (1 + (logStar n : ℝ)) := by
      have : bigD n + 1 ≤ 2 * (1 + logStar n) := by unfold dFun at hlt; omega
      exact_mod_cast this
    have hDR : (2 : ℝ) ≤ (bigD n : ℝ) := by exact_mod_cast hD2
    have hLR : (0 : ℝ) ≤ (logStar n : ℝ) := Nat.cast_nonneg _
    unfold alpha
    apply one_div_lt_one_div_of_lt (by linarith)
    linarith

end SubadditiveMMS580.Amplification
end

theorem solution : type_of% @SubadditiveMMS580.Amplification.chk_theorem_1_1 := @SubadditiveMMS580.Amplification.chk_theorem_1_1
