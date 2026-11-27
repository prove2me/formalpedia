-- Prove2me | solution 1 for PvsNP.AnchoredOnlineRun.all_prefixes_stay_in_window
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T06:29:00.095514+00:00
-- url     : https://prove2.me/submissions/f00179ca-91ad-4845-ac41-1e87bcb627fd

import Definitions.Def_AnchoredOneWorkTapeRun

set_option autoImplicit false

namespace PvsNP.AnchoredOnlineRun

open WorkBoundarySplice OnlineWindowIO

variable {S A : Type} {M : OnlineMachine S A}

theorem single_step_distance {a b : OnlineConfig S A} (one : onlineStep M a = some b) :
    a.1.head-1 ≤ b.1.head ∧ b.1.head ≤ a.1.head+1 := by
  unfold onlineStep at one
  cases cmd : M a.1.state (a.1.tape a.1.head) a.2.head? with
  | none => simp [cmd] at one
  | some row =>
    obtain ⟨next,cell,motion,consume⟩ := row
    simp only [cmd,Option.map_some,Option.some.injEq] at one
    subst b
    cases motion <;> simp [Motion.shift] <;> omega

theorem distance {a b : OnlineConfig S A} {t : ℕ} (run : OnlineRun M a b t) :
    a.1.head-(t:ℤ) ≤ b.1.head ∧ b.1.head ≤ a.1.head+(t:ℤ) := by
  induction run with
  | refl a => simp
  | next one _ ih =>
    obtain ⟨lb,ub⟩ := single_step_distance one
    omega

theorem unique {a b c : OnlineConfig S A} {n : ℕ}
    (p : OnlineRun M a b n) (q : OnlineRun M a c n) : b = c := by
  induction p generalizing c with
  | refl =>
    cases q
    rfl
  | next first _ ih =>
    cases q with
    | next other tail => cases Option.some.inj (first.symm.trans other); exact ih tail

theorem cut {a c : OnlineConfig S A} {n k : ℕ} (run : OnlineRun M a c (n+k)) :
    ∃ b, OnlineRun M a b n ∧ OnlineRun M b c k := by
  induction n generalizing a with
  | zero => exact ⟨a,.refl _,by simpa only [Nat.zero_add] using run⟩
  | succ n ih =>
    rw [Nat.succ_add] at run
    cases run with
    | next one tail =>
      obtain ⟨b,lead,rest⟩ := ih tail
      exact ⟨b,.next one lead,rest⟩

/-- Every deterministic prefix of every such run fits the same tape
window, irrespective of how many operations are composed. -/
theorem Segments.window {anchor : ℤ} {limit : ℕ}
    {a b : OnlineConfig S A} {n : ℕ} (s : Segments M anchor limit a b n) :
    ∀ c t, t ≤ n → OnlineRun M a c t →
      OnlineBoundedConsumer.InWindow (anchor-(limit:ℤ)) (2*limit+1) c.1 := by
  induction s with
  | nil atAnchor =>
    intro c t fit path
    have zero : t = 0 := by omega
    subst t
    cases path
    unfold OnlineBoundedConsumer.InWindow
    omega
  | @cons a middle b n k atAnchor fits first rest ih =>
    intro c t within path
    by_cases early : t ≤ n
    · obtain ⟨lo,hi⟩ := distance path
      unfold OnlineBoundedConsumer.InWindow
      omega
    · have nLe : n ≤ t := by omega
      have composed : OnlineRun M a c (n+(t-n)) := by simpa [Nat.add_sub_of_le nLe] using path
      obtain ⟨mid,x,y⟩ := cut composed
      obtain rfl : middle = mid := unique first x
      exact ih c (t-n) (by omega) y

end PvsNP.AnchoredOnlineRun

open PvsNP.OnlineWindowIO PvsNP.AnchoredOnlineRun

theorem solution {S A : Type} {M : OnlineMachine S A}
    {anchor : ℤ} {limit : ℕ} {a b : OnlineConfig S A} {n : ℕ}
    (s : Segments M anchor limit a b n) :
    ∀ c t, t ≤ n → OnlineRun M a c t →
      PvsNP.OnlineBoundedConsumer.InWindow (anchor-(limit:ℤ)) (2*limit+1) c.1 := s.window

#print axioms solution
