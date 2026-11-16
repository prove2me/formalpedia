-- Prove2me | solution 1 for PNormRegLib.sim_exec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:40:17.620197+00:00
-- url     : https://prove2.me/submissions/4714bae0-7f7c-4c4a-a5a9-a09ac9f9520d

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation

open PNormReg PNormRegLib SmaleNinth

namespace PNormRegLibSimAux

lemma upd_shift {α : Type*} {f g : ℕ → α} {o d n : ℕ} {x y : α}
    (hfg : ∀ i < n, f (o + i) = g i) (hxy : x = y) :
    ∀ i < n, Function.update f (o + d) x (o + i) = Function.update g d y i := by
  intro i hi
  simp only [Function.update_apply, add_right_inj]
  split_ifs
  · exact hxy
  · exact hfg i hi

lemma win_upd {α : Type*} {f g : ℤ → α} {b R z0 : ℤ} {x : α}
    (h : ∀ z, |z| ≤ R → f (b + z) = g z) :
    ∀ z, |z| ≤ R → Function.update f (z0 + b) x (b + z) = Function.update g z0 x z := by
  intro z hz
  by_cases e : z = z0
  · subst e; simp [add_comm]
  · rw [Function.update_apply, Function.update_apply, if_neg (by omega), if_neg e]
    exact h z hz

lemma out_upd {α : Type*} {f M : ℤ → α} {b R z0 : ℤ} {x : α} (hz0 : |z0| ≤ R)
    (h : ∀ y, R < |y - b| → f y = M y) :
    ∀ y, R < |y - b| → Function.update f (z0 + b) x y = M y := by
  intro y hy
  rw [Function.update_apply, if_neg]
  · exact h y hy
  · rintro rfl; simp at hy; linarith

end PNormRegLibSimAux

open PNormRegLibSimAux in
theorem solution (p : RelocParams) (F : Frame) (ω : ℕ → Bool) (ins : Instr) (X : ℤ) (r v : State)
    (hV : Valid p F) (hok : InstrOK F.nR F.nQ ins) (hA : Agree p F r v)
    (hpc : r.core.pc = p.cOff + 2 * v.core.pc) (hBd : PBounded X v) (hXR : X ≤ F.R)
    (hlive : ins ≠ .core .accept ∧ ins ≠ .core .reject ∧ ins ≠ .halt) :
    Agree p F (exec ω (p.pair ins).2 (exec ω (p.pair ins).1 r))
        (exec (fun i => ω (i + F.k)) ins v) ∧
      (exec ω (p.pair ins).2 (exec ω (p.pair ins).1 r)).core.pc =
        p.cOff + 2 * (exec (fun i => ω (i + F.k)) ins v).core.pc ∧
      (exec ω (p.pair ins).2 (exec ω (p.pair ins).1 r)).halted = r.halted ∧
      (exec (fun i => ω (i + F.k)) ins v).halted = v.halted := by
  obtain ⟨⟨rpc, rr, rp, rm⟩, ri, rc, rh, rw⟩ := r
  obtain ⟨⟨vpc, vr, vp, vm⟩, vi, vc, vh, vw⟩ := v
  obtain ⟨hR, hQ, hB0, hM, hI, hMo, hIo, hC, hW⟩ := hA
  obtain ⟨hbt, hqv⟩ := hV
  obtain ⟨hvp, hvi⟩ := hBd
  simp only at hR hQ hB0 hM hI hMo hIo hC hW hpc hvp hvi
  -- the scratch register `tmp` is invisible to the relation
  have tq : ∀ x, ∀ q < F.nQ, Function.update rp p.tmp x (p.qoff + q) = vp q := fun x q hq => by
    rw [Function.update_apply, if_neg (hqv q hq).2]; exact hQ q hq
  have tb : ∀ x, Function.update rp p.tmp x p.base = F.b := fun x => by
    rw [Function.update_apply, if_neg hbt]; exact hB0
  have qb : ∀ (f : ℕ → ℤ) x, f p.base = F.b → ∀ d < F.nQ, Function.update f (p.qoff + d) x p.base = F.b :=
    fun f x hf d hd => by rw [Function.update_apply, if_neg (hqv d hd).1.symm]; exact hf
  have inw : ∀ q, |vp q| ≤ F.R := fun q => (hvp q).trans hXR
  cases ins with
  | core i =>
    cases i with
    | const d c =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
      exact ⟨⟨upd_shift hR rfl, hQ, hB0, hM, hI, hMo, hIo, hC, by omega⟩, by omega, by simp, by simp⟩
    | add d i j =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
      exact ⟨⟨upd_shift hR (by rw [hR i hok.2.1, hR j hok.2.2]), hQ, hB0, hM, hI, hMo, hIo, hC,
        by omega⟩, by omega, by simp, by simp⟩
    | sub d i j =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
      exact ⟨⟨upd_shift hR (by rw [hR i hok.2.1, hR j hok.2.2]), hQ, hB0, hM, hI, hMo, hIo, hC,
        by omega⟩, by omega, by simp, by simp⟩
    | mul d i j =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
      exact ⟨⟨upd_shift hR (by rw [hR i hok.2.1, hR j hok.2.2]), hQ, hB0, hM, hI, hMo, hIo, hC,
        by omega⟩, by omega, by simp, by simp⟩
    | div d i j =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
      exact ⟨⟨upd_shift hR (by rw [hR i hok.2.1, hR j hok.2.2]), hQ, hB0, hM, hI, hMo, hIo, hC,
        by omega⟩, by omega, by simp, by simp⟩
    | load d q =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, exec, coreExec, Function.update_self, Agree]
      refine ⟨⟨upd_shift hR ?_, tq _, tb _, hM, hI, hMo, hIo, hC, by omega⟩, by omega, by simp, by simp⟩
      rw [hQ q hok.2, hB0, add_comm]; exact hM _ (inw q)
    | store q i =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, exec, coreExec, Function.update_self, Agree]
      rw [hR i hok.2]
      refine ⟨⟨hR, tq _, tb _, ?_, hI, ?_, hIo, hC, by omega⟩, by omega, by simp, by simp⟩
      · rw [hQ q hok.1, hB0]; exact win_upd hM
      · rw [hQ q hok.1, hB0]; exact out_upd (inw q) hMo
    | pset q c =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
      exact ⟨⟨hR, upd_shift hQ rfl, qb _ _ hB0 q hok, hM, hI, hMo, hIo, hC, by omega⟩, by omega,
        by simp, by simp⟩
    | pcopy q q' =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
      exact ⟨⟨hR, upd_shift hQ (hQ q' hok.2), qb _ _ hB0 q hok.1, hM, hI, hMo, hIo, hC, by omega⟩,
        by omega, by simp, by simp⟩
    | pinc q =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
      exact ⟨⟨hR, upd_shift hQ (by rw [hQ q hok]), qb _ _ hB0 q hok, hM, hI, hMo, hIo, hC,
        by omega⟩, by omega, by simp, by simp⟩
    | pdec q =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
      exact ⟨⟨hR, upd_shift hQ (by rw [hQ q hok]), qb _ _ hB0 q hok, hM, hI, hMo, hIo, hC,
        by omega⟩, by omega, by simp, by simp⟩
    | jle i t =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self]
      rw [hR i hok]
      split_ifs <;> simp only [Agree] <;>
        exact ⟨⟨hR, hQ, hB0, hM, hI, hMo, hIo, hC, by omega⟩, by first | trivial | omega, by simp, by simp⟩
    | pjle q q' t =>
      simp only [InstrOK] at hok
      simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self]
      rw [hQ q hok.1, hQ q' hok.2]
      split_ifs <;> simp only [Agree] <;>
        exact ⟨⟨hR, hQ, hB0, hM, hI, hMo, hIo, hC, by omega⟩, by first | trivial | omega, by simp, by simp⟩
    | accept => exact absurd rfl hlive.1
    | reject => exact absurd rfl hlive.2.1
  | pointerAdd d a b =>
    simp only [InstrOK] at hok
    simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
    exact ⟨⟨hR, upd_shift hQ (by rw [hQ a hok.2.1, hQ b hok.2.2]), qb _ _ hB0 d hok.1, hM, hI, hMo,
      hIo, hC, by omega⟩, by omega, by simp, by simp⟩
  | pointerSub d a b =>
    simp only [InstrOK] at hok
    simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
    exact ⟨⟨hR, upd_shift hQ (by rw [hQ a hok.2.1, hQ b hok.2.2]), qb _ _ hB0 d hok.1, hM, hI, hMo,
      hIo, hC, by omega⟩, by omega, by simp, by simp⟩
  | integerLoad d a =>
    simp only [InstrOK] at hok
    simp only [RelocParams.pair, exec, Function.update_self, Agree]
    refine ⟨⟨hR, upd_shift (tq _) ?_, qb _ _ (tb _) d hok.1, hM, hI, hMo, hIo, hC, by omega⟩,
      by omega, by simp, by simp⟩
    rw [hQ a hok.2, hB0, add_comm]; exact hI _ (inw a)
  | integerStore a b =>
    simp only [InstrOK] at hok
    simp only [RelocParams.pair, exec, Function.update_self, Agree]
    rw [tq _ b hok.2, hQ a hok.1, hB0]
    exact ⟨⟨hR, tq _, tb _, hM, win_upd hI, hMo, out_upd (inw a) hIo, hC, by omega⟩, by omega,
      by simp, by simp⟩
  | pointerReal d a =>
    simp only [InstrOK] at hok
    simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
    exact ⟨⟨upd_shift hR (by rw [hQ a hok.2]), hQ, hB0, hM, hI, hMo, hIo, hC, by omega⟩, by omega,
      by simp, by simp⟩
  | sqrt d a =>
    simp only [InstrOK] at hok
    simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
    exact ⟨⟨upd_shift hR (by rw [hR a hok.2]), hQ, hB0, hM, hI, hMo, hIo, hC, by omega⟩, by omega,
      by simp, by simp⟩
  | rpow d a b =>
    simp only [InstrOK] at hok
    simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
    exact ⟨⟨upd_shift hR (by rw [hR a hok.2.1, hR b hok.2.2]), hQ, hB0, hM, hI, hMo, hIo, hC,
      by omega⟩, by omega, by simp, by simp⟩
  | coin d =>
    simp only [InstrOK] at hok
    simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, Agree]
    exact ⟨⟨upd_shift hR (by rw [hC]), hQ, hB0, hM, hI, hMo, hIo, by omega, by omega⟩, by omega,
      by simp, by simp⟩
  | halt => exact absurd rfl hlive.2.2
