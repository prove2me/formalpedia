-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.BoundedSum.bounded_natural_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:09:49.733691+00:00
-- url     : https://prove2.me/submissions/fda95fd4-5fa3-47eb-922a-1958ec300c3f

import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
set_option maxHeartbeats 1600000
open scoped Classical
private lemma bsum {f : Env→ℕ} {g : Env→ℕ→ℕ} (hf : Form f)
    (hg : Form (fun ρ=>g (fun j=>ρ (j+1)) (ρ 0))) :
    Form (fun ρ=>∑i ∈ Finset.range (f ρ),g ρ i) := Form.sum hf hg
private lemma lifted {f : Env→ℕ} (hf : Form f) : Form (fun ρ=>f (fun i=>ρ (i+1))) := hf.rename Nat.succ
private lemma timesB {f g : Env→ℕ} (hf : Form f) (hg : Form g) : Form (fun ρ=>f ρ*g ρ) := by
  have s := bsum (g:=fun ρ _=>g ρ) hf (lifted hg)
  simpa using s
private lemma quotCount (a b : ℕ) :
    (∑ i ∈ Finset.range a, if (i+1)*b≤a then 1 else 0) = (if b=0 then a else a/b) := by
  by_cases h : b=0
  · simp [h]
  · have bp := Nat.pos_of_ne_zero h
    have char (i : ℕ) : (i+1)*b≤a ↔ i<a/b := by
      rw [← Nat.le_div_iff_mul_le bp];omega
    simp_rw [char]
    have filt : (Finset.range a).filter (fun i=>i<a/b)=Finset.range (a/b) := by
      ext i;simp only [Finset.mem_filter,Finset.mem_range];have hh:=Nat.div_le_self a b;omega
    rw [← Finset.sum_filter]
    simp [filt,h]
private lemma divB {f g : Env→ℕ} (hf : Form f) (hg : Form g) : Form (fun ρ=>f ρ/g ρ) := by
  let v := fun ρ : Env=>∑i ∈ Finset.range (f ρ), if (i+1)*g ρ≤f ρ then 1 else 0
  have vv : Form v :=
    bsum (g:=fun ρ i=>if (i+1)*g ρ≤f ρ then 1 else 0) hf
      (.bin .leFlag (timesB (.bin .add (.var 0) (.lit 1)) (lifted hg)) (lifted hf))
  have nz : Form (fun ρ=>if 1≤g ρ then 1 else 0) := .bin .leFlag (.lit 1) hg
  convert timesB nz vv using 1
  ext ρ
  dsimp [v]
  rw [quotCount]
  by_cases h : g ρ=0 <;> simp [h,Nat.pos_of_ne_zero]

theorem solution : (∀ f g : Env→ℕ,Form f → Form g → Form (fun ρ=>f ρ*g ρ)) ∧
    (∀ f g : Env→ℕ,Form f → Form g → Form (fun ρ=>f ρ/g ρ)) ∧
    (∀ f g : Env→ℕ,Form f → Form g → Form (fun ρ=>f ρ%g ρ)) := by
  refine ⟨fun _ _ => timesB,fun _ _ => divB,?_⟩
  intro f g hf hg
  have h : Form (fun ρ=>f ρ-g ρ*(f ρ/g ρ)) := .bin .cut hf (timesB hg (divB hf hg))
  convert h using 1
  ext ρ
  have := Nat.div_add_mod (f ρ) (g ρ)
  omega

