-- Prove2me | solution 1 for StochasticProg.IntegerLShaped.prop1_cuts_valid_for_sip
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:23:04.568907+00:00
-- url     : https://prove2.me/submissions/58b554eb-ff33-4d50-8ac2-12cb54bbde34

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Instance

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

theorem aux_p1cv_bookAdd_mono {a a' b b' : EReal} (ha : a ≤ a') (hb : b ≤ b') :
    bookAdd a b ≤ bookAdd a' b' := by
  unfold bookAdd
  by_cases h' : a' = ⊤ ∨ b' = ⊤
  · rw [if_pos h']
    exact le_top
  · rw [if_neg h']
    rw [not_or] at h'
    have h : ¬ (a = ⊤ ∨ b = ⊤) := by
      rintro (h | h)
      · exact h'.1 (top_le_iff.mp (h ▸ ha))
      · exact h'.2 (top_le_iff.mp (h ▸ hb))
    rw [if_neg h]
    exact add_le_add ha hb

theorem aux_p1cv_foldr_mono : ∀ {K : ℕ} (f g : Fin K → EReal), (∀ k, f k ≤ g k) →
    (List.ofFn f).foldr bookAdd 0 ≤ (List.ofFn g).foldr bookAdd 0
  | 0, f, g, _ => by simp
  | K + 1, f, g, hfg => by
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.foldr_cons]
    exact aux_p1cv_bookAdd_mono (hfg 0)
      (aux_p1cv_foldr_mono (fun i => f i.succ) (fun i => g i.succ) (fun i => hfg i.succ))

theorem aux_p1cv_QVal_le {n1 n2 m1 m2 K : ℕ} (d : Data n1 n2 m1 m2 K) (x : Fin n1 → ℝ)
    (k : Fin K) : QVal d.toInstance x k ≤ QValY d x k := by
  unfold QVal QValY
  apply sInf_le_sInf
  rintro z ⟨y, _, hy0, hW, hz⟩
  exact ⟨y, hy0, hW, hz⟩

theorem aux_p1cv_Q_le {n1 n2 m1 m2 K : ℕ} (d : Data n1 n2 m1 m2 K) (x : Fin n1 → ℝ) :
    Q d.toInstance x ≤ QY d x := by
  unfold Q QY
  apply aux_p1cv_foldr_mono
  intro k
  exact mul_le_mul_of_nonneg_left (aux_p1cv_QVal_le d x k)
    (EReal.coe_nonneg.mpr (d.hp_nonneg k))

end StochasticProg.IntegerLShaped

open StochasticProg.IntegerLShaped
open StochasticProg.Recourse

theorem solution {n1 n2 m1 m2 K : ℕ} (d : Data n1 n2 m1 m2 K) (x : Fin n1 → ℝ)
    (E : Fin n1 → ℝ) (e : ℝ)
    (hcut : (e : EReal) - ((dotProduct E x : ℝ) : EReal) ≤ Q d.toInstance x) :
    (e : EReal) - ((dotProduct E x : ℝ) : EReal) ≤ QY d x :=
  hcut.trans (aux_p1cv_Q_le d x)
