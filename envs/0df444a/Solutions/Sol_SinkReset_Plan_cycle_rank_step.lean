-- Prove2me | solution 1 for SinkReset.Plan.cycle_rank_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:36.876504+00:00
-- url     : https://prove2.me/submissions/8a6493ce-d978-4b62-8f4e-66e4ec1de39d

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_act_zero
public import Theorems.Thm_SinkReset_Plan_image_active_le
public import Theorems.Thm_SinkReset_Plan_kill_decreases
public import Theorems.Thm_SinkReset_Plan_delay_spec
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem word_cons {a : Letter n} {u : List (Letter n)} :
    A.IsWord (a :: u) ↔ a ∈ A.letters ∧ A.IsWord u := by
  simp [Automaton.IsWord]
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
private theorem shift_val {k m : ℕ} (q : Fin (k + m + 1)) :
    (shift k m q).val = if q.val = 0 then 0 else q.val % (k + m) + 1 := by
  by_cases h : q = 0
  · subst h; simp [shift]
  · have h' : q.val ≠ 0 := fun h'' => h (Fin.ext (by simp [h'']))
    simp [shift, h, h']
private theorem cycle_letter {k m : ℕ} (a : Letter (k + m + 1)) (ha : a ∈ (cycle k m).letters) :
    a = shift k m ∨ ∀ q, a q = q ∨ a q = 0 := by
  rcases ha with h | ⟨i, _, _, rfl⟩
  · exact Or.inl h
  · refine Or.inr fun q => ?_
    by_cases h : q = i <;> simp [kill, h]
private theorem cyc_iter {k m : ℕ} (hkm : 0 < k + m) (e : Letter (k + m + 1))
    (he : ∀ q : Fin (k + m + 1), (e q).val = if q.val = 0 then 0 else q.val % (k + m) + 1)
    (q : Fin (k + m + 1)) (hq : q.val ≠ 0) :
    ∀ s, (e^[s] q).val = (q.val - 1 + s) % (k + m) + 1 := by
  intro s
  induction s with
  | zero =>
    have := q.isLt
    rw [Function.iterate_zero_apply, add_zero, Nat.mod_eq_of_lt (by omega)]
    omega
  | succ s ih =>
    rw [Function.iterate_succ_apply', he, ih, if_neg (Nat.succ_ne_zero _), Nat.mod_add_mod,
      show q.val - 1 + s + 1 = q.val - 1 + (s + 1) by omega]
private theorem cyc_token {N : ℕ} [NeZero N] (A : Automaton N) (e : Letter N)
    (hlet : ∀ a ∈ A.letters, a = e ∨ ∀ q, a q = q ∨ a q = 0) :
    ∀ u : List (Letter N), A.IsWord u → ∀ q, act u q ≠ 0 → ∃ r ≤ u.length, act u q = e^[r] q := by
  intro u
  induction u with
  | nil => intro _ q _; exact ⟨0, le_rfl, rfl⟩
  | cons a u ih =>
    intro hu q hne
    rw [word_cons] at hu
    change act u (a q) ≠ 0 at hne
    change ∃ r ≤ u.length + 1, act u (a q) = e^[r] q
    rcases hlet a hu.1 with rfl | h
    · obtain ⟨r, hr, hrq⟩ := ih hu.2 (a q) hne
      exact ⟨r + 1, by omega, by rw [hrq, Function.iterate_succ_apply]⟩
    · rcases h q with h | h
      · rw [h] at hne ⊢
        obtain ⟨r, hr, hrq⟩ := ih hu.2 q hne
        exact ⟨r, by omega, hrq⟩
      · rw [h, act_zero A u hu.2] at hne
        exact absurd rfl hne
private theorem cyc_delta_lt {k m v s : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (δ : ℕ → ℕ)
    (hδ : ∀ v, δ v = if v = 1 then 1 else if k + 1 < v then k + m + 2 - v else 0)
    (hv : v = 1 ∨ (k + 2 ≤ v ∧ v ≤ k + m)) (hs1 : 1 ≤ s) (hsk : s ≤ k) :
    δ ((v - 1 + s) % (k + m) + 1) < δ v := by
  rcases Nat.lt_or_ge (v - 1 + s) (k + m) with h | h
  · rw [Nat.mod_eq_of_lt h, hδ, hδ]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega), hδ, hδ]
    split_ifs <;> omega
end Plan
end SinkReset
end
end

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (S : Finset (Fin (k + m + 1))) (hne : (active S).Nonempty) :
    ∃ a ∈ (cycle k m).letters, ∀ u, (cycle k m).IsWord u → u.length < k →
      cycleRank k m (S.image (act (a :: u))) < cycleRank k m S := by
  have hkm : 0 < k + m := by omega
  have hval0 : ∀ q : Fin (k + m + 1), q = 0 ↔ q.val = 0 := fun q => Fin.ext_iff
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℕ, ∀ v, δ v = if v = 1 then 1 else if k + 1 < v then k + m + 2 - v else 0 :=
    ⟨_, fun _ => rfl⟩
  have hδq : ∀ q, cycleDelta k m q = δ q.val := fun q => by rw [hδ]; rfl
  unfold cycleRank
  by_cases hK : ∃ i ∈ active S, 2 ≤ i.val ∧ i.val ≤ k + 1
  · obtain ⟨i, hi, hi2, hik⟩ := hK
    have hkli : kill i ∈ (cycle k m).letters := Or.inr ⟨i, hi2, hik, rfl⟩
    refine ⟨kill i, hkli, fun u hu _ => ?_⟩
    have hw : (cycle k m).IsWord (kill i :: u) := (word_cons _).2 ⟨hkli, hu⟩
    have hdec := kill_decreases _ S i hi (kill i :: u) hw (by
      change act u (kill i i) = 0
      rw [show kill i i = 0 from if_pos rfl]
      exact act_zero _ u hu)
    have h1 := (delay_spec hk hm (S.image (act (kill i :: u)))).1
    have h2 := Nat.mul_le_mul_left (m + 1) hdec
    rw [mul_add, mul_one] at h2
    omega
  · simp only [not_exists, not_and] at hK
    refine ⟨shift k m, Or.inl rfl, fun u hu hlen => ?_⟩
    have hw : (cycle k m).IsWord (shift k m :: u) := (word_cons _).2 ⟨Or.inl rfl, hu⟩
    have hle := image_active_le _ S (shift k m :: u) hw
    obtain ⟨q, hq, hqδ⟩ := (delay_spec hk hm S).2.1 hne
    have hq' : q ∈ S.erase 0 := hq
    have hq0 : q.val ≠ 0 := fun h => (Finset.mem_erase.1 hq').1 ((hval0 q).2 h)
    have hqO : q.val = 1 ∨ (k + 2 ≤ q.val ∧ q.val ≤ k + m) := by
      have := q.isLt
      have := hK q hq
      omega
    by_cases hp0 : act (shift k m :: u) q = 0
    · have hdec := kill_decreases _ S q hq (shift k m :: u) hw hp0
      have h1 := (delay_spec hk hm (S.image (act (shift k m :: u)))).1
      have h2 := Nat.mul_le_mul_left (m + 1) hdec
      rw [mul_add, mul_one] at h2
      omega
    · obtain ⟨r, hr, hpr⟩ := cyc_token (cycle k m) (shift k m) (fun a ha => cycle_letter a ha)
        u hu (shift k m q) hp0
      have hp : act (shift k m :: u) q = (shift k m)^[r + 1] q := by
        change act u (shift k m q) = _
        rw [hpr, Function.iterate_succ_apply]
      have hpval := cyc_iter hkm (shift k m) shift_val q hq0 (r + 1)
      have hlt := cyc_delta_lt hk hm δ hδ hqO (by omega : 1 ≤ r + 1) (by omega : r + 1 ≤ k)
      have hpmem : act (shift k m :: u) q ∈ active (S.image (act (shift k m :: u))) :=
        Finset.mem_erase.2 ⟨hp0, Finset.mem_image_of_mem _ (Finset.mem_erase.1 hq').2⟩
      have h1 := (delay_spec hk hm _).2.2 _ hpmem
      rw [hδq, hp, hpval] at h1
      rw [hδq] at hqδ
      have h2 := Nat.mul_le_mul_left (m + 1) hle
      omega
end SinkReset.Plan
