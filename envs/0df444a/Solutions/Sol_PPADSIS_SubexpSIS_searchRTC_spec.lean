-- Prove2me | solution 1 for PPADSIS.SubexpSIS.searchRTC_spec
-- status  : ACCEPTED   (prove)
-- author  : @arka
-- created : 2026-11-13T05:40:20.767894+00:00
-- url     : https://prove2.me/submissions/c4fb72b8-830e-4c53-8766-34e05fe9875e

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_SearchRTC

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

namespace SearchRTC

/-! ### Evaluating gate lists -/

/-- The wire values after running the gates `gs` on the wires `x`. -/
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.value ws]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.value x]) := rfl

lemma run_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    run (gs₁ ++ gs₂) x = run gs₂ (run gs₁ x) := by
  simp [run, List.foldl_append]

lemma run_prefix : ∀ (gs : List Gate) (x : List Bool), ∃ r, run gs x = x ++ r
  | [], x => ⟨[], by simp [run]⟩
  | g :: gs, x => by
      obtain ⟨r, hr⟩ := run_prefix gs (x ++ [g.value x])
      exact ⟨g.value x :: r, by rw [run_cons, hr]; simp⟩

lemma run_length : ∀ (gs : List Gate) (x : List Bool),
    (run gs x).length = x.length + gs.length
  | [], x => by simp [run]
  | g :: gs, x => by rw [run_cons, run_length]; simp; omega

lemma getD_append_left {l r : List Bool} {i : ℕ} (h : i < l.length) :
    (l ++ r).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma run_getD_lt (gs : List Gate) (x : List Bool) {i : ℕ} (h : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  obtain ⟨r, hr⟩ := run_prefix gs x
  rw [hr, getD_append_left h]

lemma value_append (g : Gate) (x y : List Bool) (hg : g.WF x.length) :
    g.value (x ++ y) = g.value x := by
  cases g with
  | const b => rfl
  | not i =>
      have hi : i < x.length := hg
      simp only [Gate.value, getD_append_left hi]
  | and i j =>
      have hij : i < x.length ∧ j < x.length := hg
      simp only [Gate.value, getD_append_left hij.1, getD_append_left hij.2]
  | or i j =>
      have hij : i < x.length ∧ j < x.length := hg
      simp only [Gate.value, getD_append_left hij.1, getD_append_left hij.2]

/-- The wire written by the `j`-th gate carries that gate's value on the final wire values. -/
lemma run_getD_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hwf : (gs[j]).WF (x.length + j)) :
    (run gs x).getD (x.length + j) false = (gs[j]).value (run gs x) := by
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by
    rw [List.getElem_cons_drop_succ_eq_drop, List.take_append_drop]
  set w := run (gs.take j) x with hw
  have hwl : w.length = x.length + j := by
    rw [hw, run_length, List.length_take]; omega
  have hrun : run gs x = run (gs.drop (j + 1)) (w ++ [gs[j].value w]) := by
    conv_lhs => rw [hsplit]
    rw [run_append, run_cons]
  obtain ⟨r, hr⟩ := run_prefix (gs.drop (j + 1)) (w ++ [gs[j].value w])
  rw [hrun, hr, ← hwl, List.append_assoc]
  rw [← hwl] at hwf
  rw [value_append _ _ _ hwf]
  simp

lemma run_range_getD (f : ℕ → Gate) (L : ℕ) (x : List Bool) (k : ℕ) (hk : k < L)
    (hwf : (f k).WF (x.length + k)) :
    (run ((List.range L).map f) x).getD (x.length + k) false =
      (f k).value (run ((List.range L).map f) x) := by
  have := run_getD_gate ((List.range L).map f) x k (by simpa using hk) (by simpa using hwf)
  simpa using this

lemma eval_eq_run (C : Circuit) (x : List Bool) :
    C.eval x = C.outs.map (fun o => (run C.gates x).getD o false) := rfl

lemma map_range_getD (l : List Bool) (n : ℕ) (hl : l.length = n) :
    (List.range n).map (fun i => l.getD i false) = l := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-! ### The circuits -/

/-! ### Well-formedness -/

lemma leafC_WF (φ : Circuit) (hφ : φ.WF) (h1 : φ.outs.length = 1) : (leafC φ).WF := by
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.mp h1
  have hoW : outWire φ = o := by simp [outWire, ho]
  have holt : o < φ.nIn + φ.gates.length := hφ.2.1 o (by simp [ho])
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    simp only [leafC, hoW, List.length_append, List.length_map, List.length_range] at hk ⊢
    by_cases hkG : k < φ.gates.length
    · rw [List.getElem_append_left hkG]; exact hφ.1 k hkG
    · rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_map, List.getElem_range, Gate.WF]
      omega
  · intro w hw
    simp only [leafC, hoW, List.mem_cons, List.mem_map, List.mem_range, List.length_append,
      List.length_map, List.length_range] at hw ⊢
    rcases hw with rfl | ⟨i, hi, rfl⟩ <;> omega
  · simp only [leafC, hoW]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · simp only [List.mem_map, List.mem_range, not_exists, not_and]; intro i _; omega
    · exact (List.nodup_range).map (fun a b h => by simpa using h)

lemma combC_WF (n : ℕ) : (combC n).WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    simp only [combC, List.length_map, List.length_range] at hk
    simp only [combC, List.getElem_map, List.getElem_range, combGate]
    split_ifs <;> simp only [Gate.WF] <;> omega
  · intro w hw
    simp only [combC, List.mem_cons, List.mem_map, List.mem_range, List.length_map,
      List.length_range] at hw ⊢
    rcases hw with rfl | ⟨i, hi, rfl⟩ <;> omega
  · simp only [combC]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · simp only [List.mem_map, List.mem_range, not_exists, not_and]; intro i _; omega
    · exact (List.nodup_range).map (fun a b h => by simpa using h)

lemma combAt_eq (φ : Circuit) {h : ℕ} (h1 : 1 ≤ h) (hh : h ≤ φ.nIn) :
    (PPADSIS.SubexpSIS.searchRTC φ).combAt h = combC φ.nIn := by
  simp only [RTC.combAt, searchRTC, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  rw [if_pos (by omega)]; rfl

lemma width_eq (φ : Circuit) (h1 : φ.outs.length = 1) {h : ℕ} (hh : h ≤ φ.nIn) :
    (PPADSIS.SubexpSIS.searchRTC φ).width h = φ.nIn + 1 := by
  unfold RTC.width
  split_ifs with h0
  · simp [searchRTC, leafC] <;> omega
  · rw [combAt_eq φ (by omega) hh]; simp [combC] <;> omega

lemma searchRTC_WF (φ : Circuit) (hφ : φ.WF) (h1 : φ.outs.length = 1) : (PPADSIS.SubexpSIS.searchRTC φ).WF := by
  refine ⟨by simp [searchRTC], leafC_WF φ hφ h1, rfl, ?_⟩
  intro h hh1 hh2
  have hh2' : h ≤ φ.nIn := hh2
  rw [combAt_eq φ hh1 hh2', width_eq φ h1 (by omega)]
  exact ⟨combC_WF _, by simp [combC]; ring⟩

/-! ### Size -/

lemma searchRTC_size (φ : Circuit) : (PPADSIS.SubexpSIS.searchRTC φ).size ≤ (φ.size + 2) ^ 3 := by
  simp only [RTC.size, searchRTC, leafC, combC, Circuit.size, List.map_replicate,
    List.sum_replicate, List.length_append, List.length_map, List.length_range, smul_eq_mul]
  set n := φ.nIn
  set G := φ.gates.length
  have : (n + G + 2) ^ 3 = (n + G + 2) * (n + G + 2) * (n + G + 2) := by ring
  rw [this]
  nlinarith [Nat.zero_le n, Nat.zero_le G, Nat.zero_le (n * G), Nat.zero_le (n * n)]

/-! ### Exhaustive search, recursively -/

/-- The search result, coded as `v_h + 1` bits: `(1, a)` or `(0, 0^n)`. -/
def encO (n : ℕ) : Option (List Bool) → List Bool
  | none => false :: List.replicate n false
  | some a => true :: a

/-- The first of two search results (the left one wins). -/
def firstOf : Option (List Bool) → Option (List Bool) → Option (List Bool)
  | some a, _ => some a
  | none, b => b

lemma bitsBE_length : ∀ (w a : ℕ), (bitsBE w a).length = w
  | 0, _ => rfl
  | w + 1, a => by simp [bitsBE, bitsBE_length w a]

lemma bitsBE_add_mul : ∀ (w a c : ℕ), bitsBE w (a + 2 ^ w * c) = bitsBE w a
  | 0, _, _ => rfl
  | w + 1, a, c => by
      simp only [bitsBE]
      have h1 : (a + 2 ^ (w + 1) * c) / 2 ^ w = a / 2 ^ w + 2 * c := by
        rw [pow_succ, show 2 ^ w * 2 * c = 2 ^ w * (2 * c) by ring,
          Nat.add_mul_div_left _ _ (by positivity)]
      have h2 : a + 2 ^ (w + 1) * c = a + 2 ^ w * (2 * c) := by rw [pow_succ]; ring
      rw [h1, h2, bitsBE_add_mul w a (2 * c)]
      congr 2
      simp [Nat.add_mul_mod_self_left]

lemma bitsBE_succ_lo {h k : ℕ} (hk : k < 2 ^ h) : bitsBE (h + 1) k = false :: bitsBE h k := by
  simp [bitsBE, Nat.div_eq_of_lt hk]

lemma bitsBE_succ_hi {h k : ℕ} (hk : k < 2 ^ h) :
    bitsBE (h + 1) (2 ^ h + k) = true :: bitsBE h k := by
  have hd : (2 ^ h + k) / 2 ^ h = 1 := by
    rw [Nat.add_div_left _ (by positivity), Nat.div_eq_of_lt hk]
  have ht : bitsBE h (2 ^ h + k) = bitsBE h k := by
    rw [show 2 ^ h + k = k + 2 ^ h * 1 by ring, bitsBE_add_mul]
  simp [bitsBE, hd, ht]

open Classical in
/-- The search result in the subtree of the node `η` of height `h`: the lexicographically first
`η ++ s` (`s ∈ {0,1}^h`) satisfying `P`, if any. -/
noncomputable def S (P : List Bool → Prop) (h : ℕ) (η : List Bool) : Option (List Bool) :=
  if hex : ∃ k, k < 2 ^ h ∧ P (η ++ bitsBE h k) then some (η ++ bitsBE h (Nat.find hex))
  else none

lemma S_zero (P : List Bool → Prop) (η : List Bool) :
    S P 0 η = (open Classical in if P η then some η else none) := by
  unfold S
  by_cases hp : P η
  · have hex : ∃ k, k < 2 ^ 0 ∧ P (η ++ bitsBE 0 k) := ⟨0, by norm_num, by simpa [bitsBE] using hp⟩
    rw [dif_pos hex, if_pos hp]; simp [bitsBE]
  · have hex : ¬ ∃ k, k < 2 ^ 0 ∧ P (η ++ bitsBE 0 k) := by
      rintro ⟨k, -, hk⟩; exact hp (by simpa [bitsBE] using hk)
    rw [dif_neg hex, if_neg hp]

lemma S_length (P : List Bool → Prop) (h : ℕ) (η a : List Bool) (ha : S P h η = some a) :
    a.length = η.length + h := by
  unfold S at ha
  split_ifs at ha with hex
  · cases ha; simp [bitsBE_length]

open Classical in
lemma S_succ (P : List Bool → Prop) (h : ℕ) (η : List Bool) :
    S P (h + 1) η = firstOf (S P h (η ++ [false])) (S P h (η ++ [true])) := by
  have lo : ∀ k, k < 2 ^ h → η ++ bitsBE (h + 1) k = (η ++ [false]) ++ bitsBE h k := by
    intro k hk; rw [bitsBE_succ_lo hk]; simp
  have hi : ∀ k, k < 2 ^ h → η ++ bitsBE (h + 1) (2 ^ h + k) = (η ++ [true]) ++ bitsBE h k := by
    intro k hk; rw [bitsBE_succ_hi hk]; simp
  have hpow : 2 ^ (h + 1) = 2 ^ h * 2 := pow_succ 2 h
  unfold S
  by_cases hL : ∃ k, k < 2 ^ h ∧ P ((η ++ [false]) ++ bitsBE h k)
  · have hex : ∃ k, k < 2 ^ (h + 1) ∧ P (η ++ bitsBE (h + 1) k) := by
      obtain ⟨k, hk, hp⟩ := hL
      exact ⟨k, by omega, by rw [lo k hk]; exact hp⟩
    rw [dif_pos hex, dif_pos hL]
    simp only [firstOf]
    have hs := Nat.find_spec hL
    have h1 : Nat.find hex ≤ Nat.find hL :=
      Nat.find_min' hex ⟨by omega, by rw [lo _ hs.1]; exact hs.2⟩
    have hlt : Nat.find hex < 2 ^ h := lt_of_le_of_lt h1 hs.1
    have h2 : Nat.find hL ≤ Nat.find hex :=
      Nat.find_min' hL ⟨hlt, by rw [← lo _ hlt]; exact (Nat.find_spec hex).2⟩
    rw [le_antisymm h1 h2, lo _ hs.1]
  · rw [dif_neg hL]
    simp only [firstOf]
    by_cases hR : ∃ k, k < 2 ^ h ∧ P ((η ++ [true]) ++ bitsBE h k)
    · have hs := Nat.find_spec hR
      have hex : ∃ k, k < 2 ^ (h + 1) ∧ P (η ++ bitsBE (h + 1) k) :=
        ⟨2 ^ h + Nat.find hR, by omega, by rw [hi _ hs.1]; exact hs.2⟩
      rw [dif_pos hex, dif_pos hR]
      have hge : 2 ^ h ≤ Nat.find hex := by
        by_contra hc
        push Not at hc
        exact hL ⟨_, hc, by rw [← lo _ hc]; exact (Nat.find_spec hex).2⟩
      obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = 2 ^ h + j := ⟨Nat.find hex - 2 ^ h, by omega⟩
      have hjlt : j < 2 ^ h := by have := (Nat.find_spec hex).1; omega
      have hPj : P ((η ++ [true]) ++ bitsBE h j) := by
        rw [← hi _ hjlt, ← hj]; exact (Nat.find_spec hex).2
      have h1 : Nat.find hR ≤ j := Nat.find_min' hR ⟨hjlt, hPj⟩
      have h2 : Nat.find hex ≤ 2 ^ h + Nat.find hR :=
        Nat.find_min' hex ⟨by omega, by rw [hi _ hs.1]; exact hs.2⟩
      have hjR : j = Nat.find hR := by omega
      rw [hj, hi _ hjlt, hjR]
    · have hnex : ¬ ∃ k, k < 2 ^ (h + 1) ∧ P (η ++ bitsBE (h + 1) k) := by
        rintro ⟨k, hk, hp⟩
        by_cases hk' : k < 2 ^ h
        · exact hL ⟨k, hk', by rw [← lo _ hk']; exact hp⟩
        · obtain ⟨j, rfl⟩ : ∃ j, k = 2 ^ h + j := ⟨k - 2 ^ h, by omega⟩
          exact hR ⟨j, by omega, by rw [← hi _ (by omega)]; exact hp⟩
      rw [dif_neg hnex, dif_neg hR]

/-! ### What the circuits compute -/

lemma leaf_eval (φ : Circuit) (hφ : φ.WF) (h1 : φ.outs.length = 1) (η : List Bool)
    (hη : η.length = φ.nIn) :
    (leafC φ).eval η =
      encO φ.nIn (open Classical in if φ.eval η = [true] then some η else none) := by
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.mp h1
  have hoW : outWire φ = o := by simp [outWire, ho]
  have holt : o < φ.nIn + φ.gates.length := hφ.2.1 o (by simp [ho])
  set w1 := run φ.gates η with hw1def
  have hw1 : w1.length = φ.nIn + φ.gates.length := by rw [hw1def, run_length, hη]
  set b := w1.getD o false with hb
  have hφeval : φ.eval η = [b] := by rw [eval_eq_run, ho]; rfl
  set ws := run (leafC φ).gates η with hwsdef
  have hws : ws = run ((List.range φ.nIn).map (fun i => Gate.and o i)) w1 := by
    rw [hwsdef, hw1def, ← run_append]; simp [leafC, hoW]
  have hwo : ws.getD o false = b := by rw [hws, run_getD_lt _ _ (by omega)]
  have hwi : ∀ i < φ.nIn, ws.getD (φ.nIn + φ.gates.length + i) false =
      (b && η.getD i false) := by
    intro i hi
    have := run_range_getD (fun i => Gate.and o i) φ.nIn w1 i hi
      (by simp only [Gate.WF]; omega)
    rw [hw1] at this
    rw [hws, this, ← hws]
    simp only [Gate.value, hwo]
    rw [hws, run_getD_lt _ _ (by omega), hw1def, run_getD_lt _ _ (by omega)]
  have heval : (leafC φ).eval η =
      b :: (List.range φ.nIn).map (fun i => b && η.getD i false) := by
    rw [eval_eq_run, ← hwsdef]
    have houts : (leafC φ).outs =
        o :: (List.range φ.nIn).map (fun i => φ.nIn + φ.gates.length + i) := by
      simp [leafC, hoW]
    rw [houts, List.map_cons, List.map_map]
    refine congrArg₂ _ hwo (List.map_congr_left fun i hi => ?_)
    simp only [Function.comp_apply]
    exact hwi i (List.mem_range.mp hi)
  rw [heval, hφeval]
  cases b
  · simp [encO, List.map_const']
  · simp only [encO, Bool.true_and, if_true]
    rw [map_range_getD η φ.nIn hη]

lemma comb_eval (n : ℕ) (fL fR : Bool) (aL aR : List Bool) (hL : aL.length = n)
    (hR : aR.length = n) :
    (combC n).eval ((fL :: aL) ++ (fR :: aR)) =
      (fL || fR) :: (List.range n).map (fun i => aL.getD i false || (!fL && aR.getD i false)) := by
  set x := (fL :: aL) ++ (fR :: aR) with hx
  have hxl : x.length = 2 * n + 2 := by simp [hx, hL, hR]; omega
  set ws := run (combC n).gates x with hwsdef
  have hin : ∀ j, j < 2 * n + 2 → ws.getD j false = x.getD j false :=
    fun j hj => run_getD_lt _ _ (by omega)
  have x0 : x.getD 0 false = fL := by simp [hx]
  have xL : ∀ i < n, x.getD (1 + i) false = aL.getD i false := by
    intro i hi; simp [hx, List.getD_eq_getElem?_getD, add_comm 1 i, List.getElem?_append_left (by omega : i < aL.length)]
  have xR0 : x.getD (n + 1) false = fR := by
    simp [hx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : aL.length ≤ n), hL]
  have xR : ∀ i < n, x.getD (n + 2 + i) false = aR.getD i false := by
    intro i hi
    rw [hx, show n + 2 + i = (n + 1 + i) + 1 by omega]
    simp only [List.getD_eq_getElem?_getD, List.cons_append, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by omega), hL, show n + 1 + i - n = i + 1 by omega,
      List.getElem?_cons_succ]
  have wire : ∀ k, k < 2 * n + 2 → ws.getD (2 * n + 2 + k) false = (combGate n k).value ws := by
    intro k hk
    have := run_range_getD (combGate n) (2 * n + 2) x k hk (by
      rw [hxl]; unfold combGate; split_ifs <;> simp only [Gate.WF] <;> omega)
    rw [hxl] at this; exact this
  have w0 : ws.getD (2 * n + 2) false = !fL := by
    have := wire 0 (by omega)
    simp only [combGate, if_pos] at this
    rw [show 2 * n + 2 = 2 * n + 2 + 0 by omega, this]
    simp only [Gate.value]
    rw [hin 0 (by omega), x0]
  have w1 : ws.getD (2 * n + 3) false = (fL || fR) := by
    have := wire 1 (by omega)
    simp only [combGate, show (1 : ℕ) ≠ 0 by omega, if_false, if_true] at this
    rw [show 2 * n + 3 = 2 * n + 2 + 1 by omega, this]
    simp only [Gate.value]
    rw [hin 0 (by omega), hin (n + 1) (by omega), x0, xR0]
  have wa : ∀ i < n, ws.getD (2 * n + 4 + i) false = (!fL && aR.getD i false) := by
    intro i hi
    have := wire (2 + i) (by omega)
    simp only [combGate, show 2 + i ≠ 0 by omega, show 2 + i ≠ 1 by omega,
      show 2 + i < n + 2 by omega, if_false, if_true] at this
    rw [show 2 * n + 4 + i = 2 * n + 2 + (2 + i) by omega, this]
    simp only [Gate.value]
    rw [w0, show n + (2 + i) = n + 2 + i by omega, hin _ (by omega), xR i hi]
  have wo : ∀ i < n, ws.getD (3 * n + 4 + i) false =
      (aL.getD i false || (!fL && aR.getD i false)) := by
    intro i hi
    have := wire (n + 2 + i) (by omega)
    simp only [combGate, show n + 2 + i ≠ 0 by omega, show n + 2 + i ≠ 1 by omega,
      show ¬ (n + 2 + i < n + 2) by omega, if_false] at this
    rw [show 3 * n + 4 + i = 2 * n + 2 + (n + 2 + i) by omega, this]
    simp only [Gate.value]
    rw [show n + 2 + i - n - 1 = 1 + i by omega, show n + 2 + (n + 2 + i) = 2 * n + 4 + i by omega,
      hin _ (by omega), xL i hi, wa i hi]
  rw [eval_eq_run, ← hwsdef]
  rw [show (combC n).outs = (2 * n + 3) :: (List.range n).map (fun i => 3 * n + 4 + i) from rfl,
    List.map_cons, List.map_map]
  refine congrArg₂ _ w1 (List.map_congr_left fun i hi => ?_)
  simp only [Function.comp_apply]
  exact wo i (List.mem_range.mp hi)

lemma getD_replicate_false (n i : ℕ) : (List.replicate n false).getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

lemma comb_encO (n : ℕ) (oL oR : Option (List Bool))
    (hL : ∀ a, oL = some a → a.length = n) (hR : ∀ a, oR = some a → a.length = n) :
    (combC n).eval (encO n oL ++ encO n oR) = encO n (firstOf oL oR) := by
  cases oL with
  | some a =>
    have ha := hL a rfl
    cases oR with
    | some b =>
      simp only [encO, firstOf]
      rw [comb_eval n true true a b ha (hR b rfl)]
      simp only [Bool.true_or, Bool.not_true, Bool.false_and, Bool.or_false]
      rw [map_range_getD a n ha]
    | none =>
      simp only [encO, firstOf]
      rw [comb_eval n true false a _ ha (by simp)]
      simp only [Bool.true_or, Bool.not_true, Bool.false_and, Bool.or_false]
      rw [map_range_getD a n ha]
  | none =>
    cases oR with
    | some b =>
      have hb := hR b rfl
      simp only [encO, firstOf]
      rw [comb_eval n false true _ b (by simp) hb]
      simp only [getD_replicate_false, Bool.false_or, Bool.not_false, Bool.true_and]
      rw [map_range_getD b n hb]
    | none =>
      simp only [encO, firstOf]
      rw [comb_eval n false false _ _ (by simp) (by simp)]
      simp only [getD_replicate_false, Bool.false_or, Bool.not_false, Bool.true_and,
        Bool.and_false, Bool.or_false]
      rw [List.map_const', List.length_range]

theorem nodeVal_eq (φ : Circuit) (hφ : φ.WF) (h1 : φ.outs.length = 1) :
    ∀ h, h ≤ φ.nIn → ∀ η : List Bool, η.length + h = φ.nIn →
      (PPADSIS.SubexpSIS.searchRTC φ).nodeVal h η = encO φ.nIn (S (fun a => φ.eval a = [true]) h η)
  | 0, _, η, hη => by
      rw [S_zero]
      simp only [RTC.nodeVal]
      rw [show (PPADSIS.SubexpSIS.searchRTC φ).leaf = leafC φ from rfl, leaf_eval φ hφ h1 η (by omega)]
      congr 1
      split_ifs <;> rfl
  | h + 1, hh, η, hη => by
      have IHL := nodeVal_eq φ hφ h1 h (by omega) (η ++ [false]) (by simp; omega)
      have IHR := nodeVal_eq φ hφ h1 h (by omega) (η ++ [true]) (by simp; omega)
      simp only [RTC.nodeVal]
      rw [IHL, IHR, combAt_eq φ (by omega) hh, S_succ]
      apply comb_encO
      · intro a ha; rw [S_length _ _ _ _ ha]; simp; omega
      · intro a ha; rw [S_length _ _ _ _ ha]; simp; omega

end SearchRTC

end PPADSIS.SubexpSIS

open PPADSIS.SubexpSIS PPADSIS.SubexpSIS.SearchRTC

theorem solution : ∃ k : ℕ, ∀ φ : Circuit, φ.WF → φ.outs.length = 1 →
    (searchRTC φ).WF ∧ (searchRTC φ).p = φ.nIn ∧ (searchRTC φ).size ≤ (φ.size + 2) ^ k ∧
      (searchRTC φ).output = searchOutput φ.nIn (fun a => φ.eval a = [true]) := by
  refine ⟨3, fun φ hφ h1 => ⟨searchRTC_WF φ hφ h1, rfl, searchRTC_size φ, ?_⟩⟩
  unfold RTC.output
  rw [show (searchRTC φ).p = φ.nIn from rfl, nodeVal_eq φ hφ h1 φ.nIn le_rfl [] (by simp)]
  unfold S searchOutput
  by_cases hex : ∃ k, k < 2 ^ φ.nIn ∧ φ.eval (bitsBE φ.nIn k) = [true]
  · rw [dif_pos (by simpa using hex), dif_pos hex]; rfl
  · rw [dif_neg (by simpa using hex), dif_neg hex]; rfl
