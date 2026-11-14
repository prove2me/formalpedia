-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_shearer_disc
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:36:58.001508+00:00
-- url     : https://prove2.me/submissions/b7285e33-454c-43a2-9f40-aef1085dc4b7

import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_1_1
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_memory_one_certificate
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Mathlib
set_option autoImplicit false
open LocalLemmaHierarchy.Completeness ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

private theorem numeric (d : ℕ) (hd : 3 ≤ d) (p : ℝ) (hp : 0 ≤ p)
    (hlt : p < ((d:ℝ)-1)^(d-1)/(d:ℝ)^d) :
    let c : ℝ := 1/(d:ℝ)
    0 ≤ c ∧ c < 1 ∧ p*((1-c)⁻¹)^(d-1) ≤ c ∧ p*((1-c)⁻¹)^d < 1 := by
  dsimp only
  let D : ℝ := d
  let c : ℝ := 1/D
  let A : ℝ := (1-c)⁻¹
  have hD : 3 ≤ D := by dsimp [D]; exact_mod_cast hd
  have hDp : 0 < D := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hcHalf : c < 1/2 := by dsimp [c]; apply (div_lt_iff₀ hDp).2; linarith
  have hbase : 0 < 1-c := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hd1 : 1 ≤ d := by omega
  have hpower : D^d = D^(d-1)*D := by
    have hh : d-1+1=d := Nat.sub_add_cancel hd1
    conv_lhs => rw [←hh,pow_succ]
  have hid : (D-1)^(d-1)/D^d = c*(1-c)^(d-1) := by
    rw [hpower]
    dsimp [c]
    have heq : 1-1/D = (D-1)/D := by field_simp
    rw [heq,div_pow]
    field_simp
  have hpbound : p < c*(1-c)^(d-1) := by simpa [D] using (hlt.trans_eq hid)
  have hinv : (1-c)^(d-1)*A^(d-1)=1 := by
    rw [←mul_pow]
    dsimp [A]
    rw [mul_inv_cancel₀ (ne_of_gt hbase)]
    simp
  have hbulk : p*A^(d-1) < c := by
    have hh := mul_lt_mul_of_pos_right hpbound (pow_pos hA (d-1))
    rw [mul_assoc,hinv,mul_one] at hh
    exact hh
  have hcA : c*A < 1 := by
    change c/(1-c) < 1
    exact (div_lt_one₀ hbase).2 (by linarith)
  have hroot : p*A^d < 1 := by
    have hh : d-1+1=d := Nat.sub_add_cancel hd1
    rw [←hh,pow_succ,←mul_assoc]
    exact (mul_lt_mul_of_pos_right hbulk hA).trans hcA
  exact ⟨hc.le,by linarith,hbulk.le,hroot⟩


theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (hd : 3 ≤ d) (hG : ∀ v, G.degree v ≤ d) (z : ℂ)
    (hz : ‖z‖ < ((d:ℝ)-1)^(d-1)/(d:ℝ)^d) : hardcoreZfug G z ≠ 0 := by
  classical
  by_cases hv : IsEmpty V
  · letI : IsEmpty V := hv
    have hs (s : Finset V) : s = ∅ := Finset.eq_empty_of_forall_notMem (fun v _ => isEmptyElim v)
    simp [hardcoreZfug, Finset.univ_unique, hs]
  · letI : Nonempty V := not_isEmpty_iff.mp hv
    let o : NeighborOrders G := ⟨fun _ v => (Fintype.equivFin V v).val, by
      intro v x hx y hy hxy
      exact (Fintype.equivFin V).injective (Fin.ext hxy)⟩
    let c : ℝ := 1/(d:ℝ)
    let p : ℝ := ‖z‖
    have hp : 0 ≤ p := norm_nonneg z
    have hn := numeric d hd p hp hz
    have hc0 : 0 ≤ c := hn.1
    have hc1 : c < 1 := hn.2.1
    have hbulk : p*((1-c)⁻¹)^(d-1) ≤ c := hn.2.2.1
    have hroot : p*((1-c)⁻¹)^d < 1 := hn.2.2.2
    let x : Hist (indRep G o) → ℝ := fun s => if s.moves=[] then p*((1-c)⁻¹)^d else c
    have hcert : IsMemCertificate (indRep G o) 1 (fun _ => p) x :=
      hardcore_memory_one_certificate G o d (by omega) hG p c hp hc0 hc1 hbulk hroot
    have th := theorem_1_1 G o
    have hzero := ((th.2.2.2.2 1 (fun _ => p) (fun _ => hp) x hcert) Finset.univ).1
    have h := hzero (fun _ => z) (fun _ => by simp [p])
    unfold hardcoreZfug
    simpa [indepPoly] using h
