-- Prove2me | solution 1 for PigeonholeDesign.MultiDim.theorem_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T04:05:20.550842+00:00
-- url     : https://prove2.me/submissions/16e6ddeb-b6ed-4d17-933a-c79746b08606
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_MultiDim_Stopping
import Theorems.Thm_PigeonholeDesign_MultiDim_component_1
import Theorems.Thm_PigeonholeDesign_MultiDim_component_2
import Theorems.Thm_PigeonholeDesign_MultiDim_assign_balanced

open PigeonholeDesign.Upper PigeonholeDesign.MultiDim

namespace PH9Aux

section Prefix
variable {E ι : Type*} [DecidableEq ι] {T : ℕ} (hole : E → ι) (x : Fin T → E)
  (coin : Fin T → Bool)

lemma pa_length (k : ℕ) : (prefixAssign T (cellOf hole x) (coinOf coin) k).length = k := by
  induction k with
  | zero => simp [prefixAssign]
  | succ k ih => simp [prefixAssign, ih]

lemma pa_succ (k : ℕ) : ∃ v, prefixAssign T (cellOf hole x) (coinOf coin) (k + 1) =
    prefixAssign T (cellOf hole x) (coinOf coin) k ++ [v] := ⟨_, rfl⟩

lemma pa_getD (k i : ℕ) (hi : i < k) :
    (prefixAssign T (cellOf hole x) (coinOf coin) k).getD i false =
    (prefixAssign T (cellOf hole x) (coinOf coin) (i + 1)).getD i false := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · rw [← ih h]
      obtain ⟨v, hv⟩ := pa_succ hole x coin k
      rw [hv, List.getD_append _ _ _ _ (by rw [pa_length]; exact h)]
    · subst h; rfl

lemma pa_last (n : ℕ) (h : n < T) :
    prefixAssign T (cellOf hole x) (coinOf coin) (n + 1) =
    prefixAssign T (cellOf hole x) (coinOf coin) n ++ [assign hole x coin ⟨n, h⟩] := by
  obtain ⟨v, hv⟩ := pa_succ hole x coin n
  rw [hv]
  congr 2
  unfold assign
  simp only
  rw [pa_getD hole x coin T n h, hv, List.getD_append_right _ _ _ _ (by rw [pa_length])]
  simp [pa_length]

lemma assign_eq (n : ℕ) (h : n < T) :
    assign hole x coin ⟨n, h⟩ =
      (let L := prefixAssign T (cellOf hole x) (coinOf coin) n
       let a0 := ((List.range n).zip L).countP
          (fun sb => cellOf hole x sb.1 = cellOf hole x n ∧ sb.2 = false)
       let a1 := ((List.range n).zip L).countP
          (fun sb => cellOf hole x sb.1 = cellOf hole x n ∧ sb.2 = true)
       if L.count false = T / 2 then true
          else if L.count true = T / 2 then false
          else if a0 < a1 then false
          else if a1 < a0 then true
          else coinOf coin n) := by
  have h1 := pa_last hole x coin n h
  have h2 : prefixAssign T (cellOf hole x) (coinOf coin) (n + 1) =
      prefixAssign T (cellOf hole x) (coinOf coin) n ++ [(let L := prefixAssign T (cellOf hole x) (coinOf coin) n
       let a0 := ((List.range n).zip L).countP
          (fun sb => cellOf hole x sb.1 = cellOf hole x n ∧ sb.2 = false)
       let a1 := ((List.range n).zip L).countP
          (fun sb => cellOf hole x sb.1 = cellOf hole x n ∧ sb.2 = true)
       if L.count false = T / 2 then true
          else if L.count true = T / 2 then false
          else if a0 < a1 then false
          else if a1 < a0 then true
          else coinOf coin n)] := rfl
  rw [h1] at h2
  simpa using h2


lemma card_lt_succ {T : ℕ} (P : Fin T → Prop) [DecidablePred P] (n : ℕ) (h : n < T) :
    (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n + 1 ∧ P t)).card =
      (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n ∧ P t)).card +
        if P ⟨n, h⟩ then 1 else 0 := by
  by_cases hP : P ⟨n, h⟩
  · rw [if_pos hP, ← Finset.card_insert_of_notMem (s := Finset.univ.filter
      (fun t : Fin T => (t : ℕ) < n ∧ P t)) (a := ⟨n, h⟩) (by simp)]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h3 | h3
      · exact Or.inr ⟨h3, h2⟩
      · left; exact Fin.ext h3
    · rintro (h1 | ⟨h1, h2⟩)
      · subst h1; exact ⟨by simp, hP⟩
      · exact ⟨by omega, h2⟩
  · rw [if_neg hP, add_zero]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h3 | h3
      · exact ⟨h3, h2⟩
      · have ht : t = ⟨n, h⟩ := Fin.ext h3
        exact absurd (ht ▸ h2) hP
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma pa_count (b : Bool) (n : ℕ) (hn : n ≤ T) :
    (prefixAssign T (cellOf hole x) (coinOf coin) n).count b =
      (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n ∧ assign hole x coin t = b)).card := by
  induction n with
  | zero => simp [prefixAssign]
  | succ n ih =>
    have h : n < T := by omega
    rw [pa_last hole x coin n h, List.count_append, ih (by omega),
      card_lt_succ (fun t => assign hole x coin t = b) n h]
    simp [List.count_singleton, beq_iff_eq]

lemma pa_countP (v : Option ι) (b : Bool) (n : ℕ) (hn : n ≤ T) :
    ((List.range n).zip (prefixAssign T (cellOf hole x) (coinOf coin) n)).countP
        (fun sb => cellOf hole x sb.1 = v ∧ sb.2 = b) =
      (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n ∧
        (some (hole (x t)) = v ∧ assign hole x coin t = b))).card := by
  induction n with
  | zero => simp [prefixAssign]
  | succ n ih =>
    have h : n < T := by omega
    rw [pa_last hole x coin n h, List.range_succ,
      List.zip_append (by rw [List.length_range, pa_length]), List.countP_append, ih (by omega),
      card_lt_succ (fun t => some (hole (x t)) = v ∧ assign hole x coin t = b) n h]
    simp [cellOf, h]

end Prefix

section Tau
variable {T : ℕ} (w : Fin T → Bool)

lemma find_le (P : ℕ → Bool) (d : ℕ) : ∀ (k a n : ℕ), a ≤ n → n < a + k → P n = true →
    ((List.range' a k).find? P).getD d ≤ n := by
  intro k
  induction k with
  | zero => intro a n h1 h2; omega
  | succ k ih =>
    intro a n h1 h2 hP
    rw [List.range'_succ]
    cases hPa : P a with
    | true => simpa [List.find?_cons, hPa] using h1
    | false =>
      simp only [List.find?_cons, hPa]
      have : a ≠ n := by rintro rfl; rw [hPa] at hP; exact absurd hP (by simp)
      exact ih (a + 1) n (by omega) (by omega) hP

lemma range_map_succ (T : ℕ) : (List.range T).map (· + 1) = List.range' 1 T := by
  rw [List.range'_eq_map_range]
  congr 1
  funext i
  omega

lemma tau_le : tau w ≤ T := by
  unfold tau
  generalize hf : List.find? _ _ = r
  cases r with
  | none => simp
  | some v =>
    have := List.mem_of_find?_eq_some hf
    simp at this
    simp
    omega

lemma tau_spec (n : ℕ) (h1 : 1 ≤ n) (h2 : n < tau w) :
    ¬ (nCtrl w n = T / 2 ∨ nTrt w n = T / 2) := by
  intro hP
  have hT := tau_le w
  have : tau w ≤ n := by
    unfold tau
    rw [range_map_succ]
    exact find_le _ _ T 1 n h1 (by omega) (by simpa using hP)
  omega

end Tau

section Inv
variable {ι : Type*} [DecidableEq ι] {T : ℕ} (cell : Fin T → ι) (w : Fin T → Bool)

def cnt (n : ℕ) (k : ι) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun s : Fin T => (s : ℕ) < n ∧ (cell s = k ∧ w s = b))).card

def Step2 : Prop := ∀ t : Fin T, (t : ℕ) < tau w →
  (cnt cell w t (cell t) false < cnt cell w t (cell t) true → w t = false) ∧
  (cnt cell w t (cell t) true < cnt cell w t (cell t) false → w t = true)

lemma inv (hS : Step2 cell w) : ∀ n, n ≤ tau w → ∀ k,
    cnt cell w n k false ≤ cnt cell w n k true + 1 ∧
      cnt cell w n k true ≤ cnt cell w n k false + 1 := by
  intro n
  induction n with
  | zero => intro _ k; simp [cnt]
  | succ n ih =>
    intro hn k
    have hT : n < T := lt_of_lt_of_le (by omega) (tau_le w)
    have h0 := ih (by omega) k
    have hS' := hS ⟨n, hT⟩ (by simp; omega)
    simp only [cnt] at h0 hS' ⊢
    rw [card_lt_succ _ n hT, card_lt_succ _ n hT]
    by_cases hk : cell ⟨n, hT⟩ = k
    · subst hk
      cases hw : w ⟨n, hT⟩ <;> simp [hw] at hS' ⊢ <;> omega
    · simp [hk]; omega

lemma cnt_add (n : ℕ) (k : ι) : cnt cell w n k false + cnt cell w n k true =
    (Finset.univ.filter (fun s : Fin T => (s : ℕ) < n ∧ cell s = k)).card := by
  rw [← Finset.card_filter_add_card_filter_not (fun s => w s = false)]
  simp only [cnt, Finset.filter_filter]
  congr 2 <;> ext s <;> simp [and_assoc]

lemma cell_balanced (hS : Step2 cell w) (k : ι) :
    (Finset.univ.filter (fun t => t ∈ matched cell w ∧ (cell t = k ∧ w t = false))).card =
    (Finset.univ.filter (fun t => t ∈ matched cell w ∧ (cell t = k ∧ w t = true))).card := by
  set P := Finset.univ.filter (fun s : Fin T => (s : ℕ) < tau w ∧ cell s = k) with hP
  have key : ∀ n, n ≤ tau w →
      Even (Finset.univ.filter (fun s : Fin T => (s : ℕ) < n ∧ cell s = k)).card →
      cnt cell w n k false = cnt cell w n k true := by
    intro n hn he
    have h1 := inv cell w hS n hn k
    have h2 := cnt_add cell w n k
    obtain ⟨r, hr⟩ := he
    omega
  rcases Nat.even_or_odd P.card with he | ho
  · have e : ∀ b, (Finset.univ.filter (fun t => t ∈ matched cell w ∧ (cell t = k ∧ w t = b))) =
        Finset.univ.filter (fun s : Fin T => (s : ℕ) < tau w ∧ (cell s = k ∧ w s = b)) := by
      intro b; ext t
      simp only [matched, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, _⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨h1, Or.inl ?_⟩, h2, h3⟩
        subst h2; exact he
    rw [e, e]; exact key _ le_rfl he
  · have hne : P.Nonempty := by
      rw [← Finset.card_pos]; obtain ⟨r, hr⟩ := ho; omega
    set ℓ := P.max' hne with hℓdef
    have hℓ : ℓ ∈ P := P.max'_mem hne
    have hℓ' : (ℓ : ℕ) < tau w ∧ cell ℓ = k := by simpa [hP] using hℓ
    have e : ∀ b, (Finset.univ.filter (fun t => t ∈ matched cell w ∧ (cell t = k ∧ w t = b))) =
        Finset.univ.filter (fun s : Fin T => (s : ℕ) < (ℓ : ℕ) ∧ (cell s = k ∧ w s = b)) := by
      intro b; ext t
      simp only [matched, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, h4⟩, h2, h3⟩
        refine ⟨?_, h2, h3⟩
        rcases h4 with h4 | ⟨s', hs1, hs2, hs3⟩
        · exfalso; subst h2; exact (Nat.not_even_iff_odd.2 ho) h4
        · have hs' : s' ∈ P := by simp [hP]; exact ⟨hs2, hs3.trans h2⟩
          have := P.le_max' s' hs'
          exact lt_of_lt_of_le (Fin.lt_def.1 hs1) (Fin.le_def.1 this)
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨by omega, Or.inr ⟨ℓ, Fin.lt_def.2 h1, hℓ'.1, hℓ'.2.trans h2.symm⟩⟩, h2, h3⟩
    rw [e, e]
    apply key _ (le_of_lt hℓ'.1)
    have hPe : P = insert ℓ (Finset.univ.filter (fun s : Fin T => (s : ℕ) < ℓ ∧ cell s = k)) := by
      ext s; simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hs : s = ℓ
        · left; exact hs
        · right; refine ⟨?_, h2⟩
          have := P.le_max' s (by simp [hP]; exact ⟨h1, h2⟩)
          exact Fin.lt_def.1 (lt_of_le_of_ne this hs)
      · rintro (rfl | ⟨h1, h2⟩)
        · exact hℓ'
        · exact ⟨by omega, h2⟩
    rw [hPe, Finset.card_insert_of_notMem (by simp)] at ho
    obtain ⟨r, hr⟩ := ho; exact ⟨r, by omega⟩

lemma exists_cell_equiv (hS : Step2 cell w) :
    ∃ e : {t // t ∈ matched cell w ∧ w t = false} ≃ {t // t ∈ matched cell w ∧ w t = true},
      ∀ a, cell (e a).1 = cell a.1 := by
  have hcard : ∀ k : ι,
      Fintype.card {a : {t // t ∈ matched cell w ∧ w t = false} // cell a.1 = k} =
      Fintype.card {b : {t // t ∈ matched cell w ∧ w t = true} // cell b.1 = k} := by
    intro k
    have h := cell_balanced cell w hS k
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun t => t ∈ matched cell w ∧ w t = false) (fun t => cell t = k)),
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun t => t ∈ matched cell w ∧ w t = true) (fun t => cell t = k)),
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype]
    convert h using 2 <;> ext t <;> simp <;> tauto
  refine ⟨(Equiv.sigmaFiberEquiv (fun a : {t // t ∈ matched cell w ∧ w t = false} => cell a.1)).symm.trans
    ((Equiv.sigmaCongrRight (fun k => Fintype.equivOfCardEq (hcard k))).trans
      (Equiv.sigmaFiberEquiv (fun b : {t // t ∈ matched cell w ∧ w t = true} => cell b.1))), ?_⟩
  intro a
  simp only [Equiv.trans_apply, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    Equiv.sigmaCongrRight_apply]
  exact ((Fintype.equivOfCardEq (hcard (cell a.1))) ⟨a, rfl⟩).2

end Inv

lemma step2_design {E ι : Type*} [DecidableEq ι] {T : ℕ} (hT : 2 ≤ T) (hole : E → ι)
    (x : Fin T → E) (coin : Fin T → Bool) :
    Step2 (fun t => hole (x t)) (assign hole x coin) := by
  intro t ht
  have hspec : ¬ (nCtrl (assign hole x coin) t = T / 2 ∨ nTrt (assign hole x coin) t = T / 2) := by
    rcases Nat.eq_zero_or_pos (t : ℕ) with h0 | h0
    · rw [h0]; simp [nCtrl, nTrt]; omega
    · exact tau_spec _ t h0 ht
  have heq := assign_eq hole x coin t t.2
  simp only [Fin.eta] at heq
  rw [pa_count hole x coin false t (le_of_lt t.2), pa_count hole x coin true t (le_of_lt t.2),
    pa_countP hole x coin _ false t (le_of_lt t.2),
    pa_countP hole x coin _ true t (le_of_lt t.2)] at heq
  simp only [nCtrl, nTrt] at hspec
  push Not at hspec
  rw [if_neg hspec.1, if_neg hspec.2] at heq
  have hc : cellOf hole x t = some (hole (x t)) := by simp [cellOf, t.2]
  simp only [hc, Option.some.injEq] at heq
  unfold cnt
  constructor
  · intro h; rw [heq, if_pos h]
  · intro h; rw [heq, if_neg (not_lt.2 h.le), if_pos h]

lemma cell_dist {m : ℕ} (hm : 1 ≤ m) (z z' : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hz' : z' ∈ Set.Icc (0 : ℝ) 1)
    (h : min ⌊z * m⌋₊ (m - 1) = min ⌊z' * m⌋₊ (m - 1)) : |z - z'| ≤ 1 / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have key : ∀ y ∈ Set.Icc (0 : ℝ) 1, ((min ⌊y * m⌋₊ (m - 1) : ℕ) : ℝ) ≤ y * m ∧
      y * m ≤ ((min ⌊y * m⌋₊ (m - 1) : ℕ) : ℝ) + 1 := by
    intro y hy
    have hy0 : 0 ≤ y * m := mul_nonneg hy.1 hmpos.le
    constructor
    · calc ((min ⌊y * m⌋₊ (m - 1) : ℕ) : ℝ) ≤ (⌊y * m⌋₊ : ℝ) := by
            exact_mod_cast min_le_left _ _
        _ ≤ y * m := Nat.floor_le hy0
    · rcases le_total ⌊y * m⌋₊ (m - 1) with h1 | h1
      · rw [min_eq_left h1]; exact (Nat.lt_floor_add_one _).le
      · rw [min_eq_right h1]; push_cast [Nat.cast_sub hm]; nlinarith [hy.2]
  obtain ⟨a1, a2⟩ := key z hz
  obtain ⟨b1, b2⟩ := key z' hz'
  rw [h] at a1 a2
  rw [abs_sub_le_iff]
  constructor <;> rw [le_div_iff₀ hmpos] <;> nlinarith

lemma grid_dist {q p m : ℕ} (hm : 1 ≤ m) (z z' : Cov q p)
    (hz : ∀ j, z (Sum.inr j) ∈ Set.Icc (0 : ℝ) 1) (hz' : ∀ j, z' (Sum.inr j) ∈ Set.Icc (0 : ℝ) 1)
    (h : gridHole m z = gridHole m z') : dist z z' ≤ Real.sqrt p / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : ∀ i, z (Sum.inl i) = z' (Sum.inl i) := fun i => congrFun (congrArg Prod.fst h) i
  have h2 : ∀ j, |z (Sum.inr j) - z' (Sum.inr j)| ≤ 1 / m := fun j =>
    cell_dist hm _ _ (hz j) (hz' j) (congrFun (congrArg Prod.snd h) j)
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i, dist (z i) (z' i) ^ 2) ≤ Real.sqrt (p * (1 / (m : ℝ)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [Fintype.sum_sum_type]
        have : ∑ i : Fin q, dist (z (Sum.inl i)) (z' (Sum.inl i)) ^ 2 = 0 := by simp [h1]
        rw [this, zero_add]
        calc ∑ j : Fin p, dist (z (Sum.inr j)) (z' (Sum.inr j)) ^ 2
            ≤ ∑ j : Fin p, (1 / (m : ℝ)) ^ 2 := by
              apply Finset.sum_le_sum; intro j _
              rw [Real.dist_eq]
              exact pow_le_pow_left₀ (abs_nonneg _) (h2 j) 2
          _ = p * (1 / (m : ℝ)) ^ 2 := by simp
    _ = Real.sqrt p / m := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]; ring


lemma disc_split {E : Type*} [PseudoMetricSpace E] {T : ℕ} (x : Fin T → E) (w : Fin T → Bool)
    (M : Finset (Fin T))
    (h1 : Fintype.card {t // t ∈ M ∧ w t = false} = Fintype.card {t // t ∈ M ∧ w t = true})
    (h2 : Fintype.card {t // t ∈ Finset.univ \ M ∧ w t = false} =
      Fintype.card {t // t ∈ Finset.univ \ M ∧ w t = true}) :
    discrepancy x w ≤ discrepancyOn x w M + discrepancyOn x w (Finset.univ \ M) := by
  obtain ⟨e1'⟩ := Fintype.card_eq.1 h1
  obtain ⟨e2'⟩ := Fintype.card_eq.1 h2
  have hM : ∀ t, t ∈ Finset.univ \ M ↔ t ∉ M := by simp
  have key : ∀ (e1 : {t // t ∈ M ∧ w t = false} ≃ {t // t ∈ M ∧ w t = true})
      (e2 : {t // t ∈ Finset.univ \ M ∧ w t = false} ≃ {t // t ∈ Finset.univ \ M ∧ w t = true}),
      discrepancy x w ≤ (∑ a, dist (x a.1) (x (e1 a).1)) + ∑ a, dist (x a.1) (x (e2 a).1) := by
    intro e1 e2
    let f : {t // w t = false} → {t // w t = true} := fun a =>
      if h : a.1 ∈ M then ⟨(e1 ⟨a.1, h, a.2⟩).1, (e1 ⟨a.1, h, a.2⟩).2.2⟩
      else ⟨(e2 ⟨a.1, (hM _).2 h, a.2⟩).1, (e2 ⟨a.1, (hM _).2 h, a.2⟩).2.2⟩
    let g : {t // w t = true} → {t // w t = false} := fun b =>
      if h : b.1 ∈ M then ⟨(e1.symm ⟨b.1, h, b.2⟩).1, (e1.symm ⟨b.1, h, b.2⟩).2.2⟩
      else ⟨(e2.symm ⟨b.1, (hM _).2 h, b.2⟩).1, (e2.symm ⟨b.1, (hM _).2 h, b.2⟩).2.2⟩
    have hfg : ∀ a, g (f a) = a := by
      intro a
      by_cases h : a.1 ∈ M
      · have hm : (e1 ⟨a.1, h, a.2⟩).1 ∈ M := (e1 ⟨a.1, h, a.2⟩).2.1
        simp only [f, g, dif_pos h, dif_pos hm]
        apply Subtype.ext; simp
      · have hm : (e2 ⟨a.1, (hM _).2 h, a.2⟩).1 ∉ M := (hM _).1 (e2 ⟨a.1, (hM _).2 h, a.2⟩).2.1
        simp only [f, g, dif_neg h, dif_neg hm]
        apply Subtype.ext; simp
    have hgf : ∀ b, f (g b) = b := by
      intro b
      by_cases h : b.1 ∈ M
      · have hm : (e1.symm ⟨b.1, h, b.2⟩).1 ∈ M := (e1.symm ⟨b.1, h, b.2⟩).2.1
        simp only [f, g, dif_pos h, dif_pos hm]
        apply Subtype.ext; simp
      · have hm : (e2.symm ⟨b.1, (hM _).2 h, b.2⟩).1 ∉ M :=
          (hM _).1 (e2.symm ⟨b.1, (hM _).2 h, b.2⟩).2.1
        simp only [f, g, dif_neg h, dif_neg hm]
        apply Subtype.ext; simp
    let e : {t // w t = false} ≃ {t // w t = true} := ⟨f, g, hfg, hgf⟩
    have hle : discrepancy x w ≤ ∑ a, dist (x a.1) (x (e a).1) :=
      ciInf_le ⟨0, by rintro _ ⟨e', rfl⟩; exact Finset.sum_nonneg (fun _ _ => dist_nonneg)⟩ e
    refine hle.trans (le_of_eq ?_)
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : {t // w t = false} => a.1 ∈ M)]
    congr 1
    · refine Finset.sum_bij' (fun a ha => ⟨a.1, (Finset.mem_filter.1 ha).2, a.2⟩)
        (fun a _ => ⟨a.1, a.2.2⟩) (by simp) (fun a _ => by simpa using a.2.1) (by simp) (by simp) ?_
      intro a ha
      have h := (Finset.mem_filter.1 ha).2
      simp only [e, Equiv.coe_fn_mk, f, dif_pos h]
    · refine Finset.sum_bij' (fun a ha => ⟨a.1, (hM _).2 (Finset.mem_filter.1 ha).2, a.2⟩)
        (fun a _ => ⟨a.1, a.2.2⟩) (by simp) (fun a _ => by simpa using ((hM _).1 a.2.1))
        (by simp) (by simp) ?_
      intro a ha
      have h := (Finset.mem_filter.1 ha).2
      simp only [e, Equiv.coe_fn_mk, f, dif_neg h]
  have hb : ∀ e2 : {t // t ∈ Finset.univ \ M ∧ w t = false} ≃
      {t // t ∈ Finset.univ \ M ∧ w t = true},
      discrepancy x w - ∑ a, dist (x a.1) (x (e2 a).1) ≤ discrepancyOn x w M := by
    intro e2
    have : Nonempty ({t // t ∈ M ∧ w t = false} ≃ {t // t ∈ M ∧ w t = true}) := ⟨e1'⟩
    exact le_ciInf (fun e1 => by linarith [key e1 e2])
  have : Nonempty ({t // t ∈ Finset.univ \ M ∧ w t = false} ≃
      {t // t ∈ Finset.univ \ M ∧ w t = true}) := ⟨e2'⟩
  have : discrepancy x w - discrepancyOn x w M ≤ discrepancyOn x w (Finset.univ \ M) :=
    le_ciInf (fun e2 => by linarith [hb e2])
  linarith

end PH9Aux


open PH9Aux in
theorem solution (p q : ℕ) (hp : 2 ≤ p) (S : Fin q → Finset ℝ)
    (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1) (φ c : ℝ) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hc : 1 < c) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → Cov q p, Admissible S x →
        PigeonholeDesign.Upper.phdExp (gridHole (cellsPerAxis p c φ T)) x
          ≤ C * ((T : ℝ) ^ ((1 : ℝ) - φ) + (T : ℝ) ^ (((p : ℝ) - 1) * φ) *
                  (if p = 2 then Real.log T ^ ((3 : ℝ) / 2) else 1)) := by
  obtain ⟨C2, hC2, T₂, h2⟩ := PigeonholeDesign.MultiDim.component_2 p q hp S hS φ c hφ0 hφ1 hc
  set K1 := (1 / 2) * c ^ ((1 : ℝ) / p) * Real.sqrt p with hK1def
  have hcpos : (0 : ℝ) < c := by linarith
  have hppos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hK1 : 0 < K1 := by
    have := Real.sqrt_pos.2 hppos
    positivity
  refine ⟨max K1 C2, lt_max_of_lt_left hK1, max T₂ 1, ?_⟩
  intro T hT hTe x hx
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT2 : 2 ≤ T := by obtain ⟨r, hr⟩ := hTe; omega
  set m := cellsPerAxis p c φ T with hm
  have hsplit : ∀ coin : Fin T → Bool,
      discrepancy x (assign (gridHole m) x coin) ≤
        K1 * (T : ℝ) ^ ((1 : ℝ) - φ) + discrepancyOn x (assign (gridHole m) x coin)
          (Finset.univ \ matched (fun t => gridHole m (x t)) (assign (gridHole m) x coin)) := by
    intro coin
    set cell := fun t => gridHole m (x t) with hcell
    set w := assign (gridHole m) x coin with hw
    obtain ⟨e, -⟩ := exists_cell_equiv cell w (step2_design hT2 (gridHole m) x coin)
    have hbal := PigeonholeDesign.MultiDim.assign_balanced T hTe (gridHole m) x coin
    have hf : (Finset.univ.filter (fun t => w t = false)).card = T / 2 := hbal.1
    have ht : (Finset.univ.filter (fun t => w t = true)).card = T / 2 := hbal.2
    have h1 := Fintype.card_congr e
    have hb : ∀ b : Bool, Fintype.card {t // t ∈ Finset.univ \ matched cell w ∧ w t = b} +
        Fintype.card {t // t ∈ matched cell w ∧ w t = b} =
          (Finset.univ.filter (fun t => w t = b)).card := by
      intro b
      rw [Fintype.card_subtype, Fintype.card_subtype,
        ← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun t => w t = b))
          (fun t => t ∉ matched cell w), Finset.filter_filter, Finset.filter_filter]
      congr 1 <;> (congr 1; ext t; simp; try tauto)
    have h2' : Fintype.card {t // t ∈ Finset.univ \ matched cell w ∧ w t = false} =
        Fintype.card {t // t ∈ Finset.univ \ matched cell w ∧ w t = true} := by
      have := hb false; have := hb true; omega
    have hsp := disc_split x w (matched cell w) h1 h2'
    have hc1 : discrepancyOn x w (matched cell w) ≤ K1 * (T : ℝ) ^ ((1 : ℝ) - φ) :=
      PigeonholeDesign.MultiDim.component_1 p q hp S φ c hφ0 hφ1 hc T hT1 hTe x hx coin
    exact hsp.trans (add_le_add_left hc1 _)
  have hC2' := h2 T (le_trans (le_max_left _ _) hT) hTe x hx
  have hpow : (0 : ℝ) < 2 ^ T := by positivity
  rw [div_le_iff₀ hpow] at hC2'
  unfold phdExp
  rw [div_le_iff₀ hpow]
  have hsum := Finset.sum_le_sum (fun coin (_ : coin ∈ (Finset.univ : Finset (Fin T → Bool))) =>
    hsplit coin)
  have hcard : ((Finset.univ : Finset (Fin T → Bool)).card : ℝ) = 2 ^ T := by simp
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  have hA : 0 ≤ (T : ℝ) ^ ((1 : ℝ) - φ) := by positivity
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast hT1)
  have hL : 0 ≤ (if p = 2 then Real.log T ^ ((3 : ℝ) / 2) else 1) := by
    split_ifs
    · exact Real.rpow_nonneg hlog _
    · norm_num
  have hBL : 0 ≤ (T : ℝ) ^ (((p : ℝ) - 1) * φ) *
      (if p = 2 then Real.log T ^ ((3 : ℝ) / 2) else 1) := mul_nonneg (by positivity) hL
  have hfin : K1 * (T : ℝ) ^ ((1 : ℝ) - φ) + C2 * (T : ℝ) ^ (((p : ℝ) - 1) * φ) *
      (if p = 2 then Real.log T ^ ((3 : ℝ) / 2) else 1) ≤
      max K1 C2 * ((T : ℝ) ^ ((1 : ℝ) - φ) + (T : ℝ) ^ (((p : ℝ) - 1) * φ) *
        (if p = 2 then Real.log T ^ ((3 : ℝ) / 2) else 1)) := by
    have e1 := mul_le_mul_of_nonneg_right (le_max_left K1 C2) hA
    have e2 := mul_le_mul_of_nonneg_right (le_max_right K1 C2) hBL
    rw [mul_add]
    linarith [mul_assoc C2 ((T : ℝ) ^ (((p : ℝ) - 1) * φ))
      (if p = 2 then Real.log T ^ ((3 : ℝ) / 2) else 1)]
  have := mul_le_mul_of_nonneg_right hfin hpow.le
  nlinarith
