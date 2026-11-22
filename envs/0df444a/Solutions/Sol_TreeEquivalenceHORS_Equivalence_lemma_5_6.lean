-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T17:52:44.00472+00:00
-- url     : https://prove2.me/submissions/7b331369-3c85-452d-88f4-fe4ebc731eef

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_3
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_5

namespace TreeEquivalenceHORS.Equivalence

private theorem headConv_step {G : HORS} {t u : Tm} (step : G.HeadStep t u) (a : ℕ) (us : List Tm) :
    G.HeadConv t a us ↔ G.HeadConv u a us := by
  constructor
  · rintro ⟨s, hs, spine⟩
    rcases hs.cases_head with rfl | ⟨s', h', htail⟩
    · simp [HORS.HeadStep, HORS.headStep, spine] at step
    · have eq : u = s' := Option.some.inj (step.symm.trans h')
      exact ⟨s, eq ▸ htail, spine⟩
  · rintro ⟨s, hs, spine⟩
    exact ⟨s, hs.head step, spine⟩

theorem obs_step {G : HORS} {t u : Tm} (hs : G.HeadStep t u) (w : List ℕ) (c : ℕ) :
    G.Obs t w c ↔ G.Obs u w c := by
  cases w <;> simp only [HORS.Obs, headConv_step hs]

theorem terminal_conv {G : HORS} {t : Tm} {c : ℕ} {args : List Tm}
    (head : t.spine = (.tm c, args)) (a : ℕ) (us : List Tm) :
    G.HeadConv t a us ↔ c = a ∧ args = us := by
  constructor
  · rintro ⟨t', hs, h⟩
    rcases hs.cases_head with rfl | ⟨v, step, _⟩
    · simpa [head] using h
    · simp [HORS.HeadStep, HORS.headStep, head] at step
  · rintro ⟨rfl, rfl⟩
    exact ⟨t, .refl, head⟩

theorem step_control (side : Side) (M : Machine) {i : ℕ} (hi : i ≤ M.length) (t : StateArgs) :
    (compile side M).headStep (Tm.apps (.nt (iF i)) t.toList) =
      some ((ctrlBody side M i).subst t.toList) := by
  have hsp : (Tm.apps (.nt (iF i)) t.toList).spine = (.nt (iF i), t.toList) := rfl
  have hty : (compile side M).nts[iF i]? = some tyF := by
    rw [show iF i = i + 13 by unfold iF; omega]
    exact List.getElem?_replicate_of_lt (Nat.lt_succ_of_le hi)
  have hr : (compile side M).rules[iF i]? = some (ctrlBody side M i) := by
    rw [show iF i = i + 13 by unfold iF; omega]
    change ((List.range (M.length + 1)).map (ctrlBody side M))[i]? = _
    simp [List.getElem?_range (Nat.lt_succ_of_le hi)]
  simp only [HORS.headStep, hsp, hty, hr]
  rfl

private theorem obs_z (G : HORS) (w : List ℕ) (a : Fin 3) :
    G.Obs tz w a.val ↔ zVal w = some a := by
  have conv := terminal_conv (G := G) (t := tz) (c := 0) (args := []) rfl
  cases w <;> simp [HORS.Obs, conv, zVal, Fin.ext_iff]

private theorem obs_b_root (G : HORS) (x y z : Tm) (a : Fin 3) :
    G.Obs (Tm.apps tb [x,y,z]) [] a.val ↔ (some 2 : Option (Fin 3)) = some a := by
  have conv := terminal_conv (G := G) (t := Tm.apps tb [x,y,z]) (c := 2) (args := [x,y,z]) rfl
  simp [HORS.Obs, conv, Fin.ext_iff]

private theorem obs_b_child (G : HORS) (x y z : Tm) (i : ℕ) (w : List ℕ) (c : ℕ) :
    G.Obs (Tm.apps tb [x,y,z]) (i :: w) c ↔
      match i with
      | 0 => G.Obs x w c
      | 1 => G.Obs y w c
      | 2 => G.Obs z w c
      | _ => False := by
  have conv := terminal_conv (G := G) (t := Tm.apps tb [x,y,z]) (c := 2) (args := [x,y,z]) rfl
  rcases i with _ | _ | _ | i <;> simp [HORS.Obs, conv]

private theorem obs_K (side : Side) (M : Machine) (w : List ℕ) (a : Fin 3) :
    (compile side M).Obs (.nt iK) w a.val ↔ kVal w = some a := by
  have step : (compile side M).HeadStep (.nt iK) (Tm.apps tb [tz, .nt iK, .nt iK]) := rfl
  induction w with
  | nil => exact (obs_step step [] a).trans (obs_b_root ..)
  | cons i w ih =>
    rw [obs_step step, obs_b_child]
    rcases i with _ | _ | _ | i <;> simp [kVal, obs_z, ih]

private def haltNum (side : Side) (t : StateArgs) : Tm :=
  match side with | .L => t.h | .R => t.k

private theorem halt_step (side : Side) (M : Machine) {i : ℕ} (hi : ¬ M.Active i) (t : StateArgs) :
    (compile side M).HeadStep (callF M i t.toList)
      (Tm.apps tb [Tm.apps (haltNum side t) [ta, tz], .nt iK, .nt iK]) := by
  unfold HORS.HeadStep callF Machine.norm
  rw [if_neg hi, step_control side M (Nat.zero_le _)]
  cases side <;> rfl

private theorem halt_real (side : Side) (M : Machine) (m : ℕ) (t : StateArgs) (R : PairState)
    (ht : Reg (compile side M) m t R) :
    Real (compile side M) .o (Tm.apps (haltNum side t) [ta,tz]) (chainVal (side.pick R.W)) := by
  obtain ⟨_, _, _, _, obs⟩ := lemma_5_3 side M
  cases side
  · exact obs _ _ ht.2.2.2.2.2.1
  · exact obs _ _ ht.2.2.2.2.2.2

private theorem proved_here (side : Side) (M : Machine) (m i : ℕ) (t : StateArgs) (R : PairState)
    (hR : Reg (compile side M) m t R) (w : List ℕ) (a : Fin 3) :
    (compile side M).Obs (callF M i t.toList) w a.val ↔ Tmap side M m i R w = some a := by
  induction w generalizing m i t R with
  | nil =>
    by_cases hi : M.Active i
    · obtain ⟨hs, _⟩ := (lemma_5_5 side M).1 m i t R hi hR
      simpa only [callF, Machine.norm, if_pos hi, Tmap] using
        (obs_step hs [] a).trans (obs_b_root ..)
    · exact (obs_step (halt_step side M hi t) [] a).trans (obs_b_root ..)
  | cons c w ih =>
    by_cases hi : M.Active i
    · obtain ⟨hs, hr⟩ := (lemma_5_5 side M).1 m i t R hi hR
      have call : callF M i t.toList = Tm.apps (.nt (iF i)) t.toList := by simp [callF, Machine.norm, hi]
      rw [call, obs_step hs, obs_b_child]
      rcases c with _ | _ | _ | c <;> simp [Tmap, hi, obs_z, ih _ _ _ _ (hr .one), ih _ _ _ _ (hr .two)]
    · rw [obs_step (halt_step side M hi t), obs_b_child]
      rcases c with _ | _ | _ | c <;> simp [Tmap, hi, halt_real side M m t R hR w a, obs_K]

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (side : Side) (M : Machine) (m i : ℕ) (t : StateArgs) (R : PairState)
    (hR : Reg (compile side M) m t R) (w : List ℕ) (a : Fin 3) :
    (compile side M).Obs (callF M i t.toList) w a.val ↔ Tmap side M m i R w = some a := proved_here side M m i t R hR w a
