-- Prove2me | solution 1 for RHHeight1000.em_t48711_head40_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T10:13:02.246189+00:00
-- url     : https://prove2.me/submissions/2d684d58-67e8-40eb-9a75-dd471f26ecf6

import Mathlib
set_option Elab.async false
set_option maxErrors 100
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort121
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel






end Zeta.RiemannSiegel
end
end CertificatePort121


section CertificatePort122
section
open Filter MeasureTheory Set Topology
open scoped Real
namespace Real


end Real
namespace Complex






end Complex
namespace Real


end Real
end
end CertificatePort122


section CertificatePort123
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel






























end Zeta.RiemannSiegel
end
end CertificatePort123


section CertificatePort124
section
open Complex Filter MeasureTheory Topology
open scoped Real
namespace Zeta.RiemannSiegel








end Zeta.RiemannSiegel
end
end CertificatePort124


section CertificatePort125
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel














end Zeta.RiemannSiegel
end
end CertificatePort125


section CertificatePort126
section
open Complex Filter MeasureTheory Topology
open scoped Real
namespace Zeta.RiemannSiegel








































end Zeta.RiemannSiegel
end
end CertificatePort126


section CertificatePort127
section
open Complex MeasureTheory Set
open scoped Real
namespace Zeta.RiemannSiegel






























































end Zeta.RiemannSiegel
end
end CertificatePort127


section CertificatePort128
section
open Complex Filter
open scoped Real Topology
namespace Zeta.RiemannSiegel










end Zeta.RiemannSiegel
end
end CertificatePort128


section CertificatePort129
section
open Complex
open scoped Real
namespace Zeta.RiemannSiegel










end Zeta.RiemannSiegel
end
end CertificatePort129


section CertificatePort130
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel






















end Zeta.RiemannSiegel
open Zeta.RiemannSiegel




end
end CertificatePort130


section CertificatePort131
section









end
end CertificatePort131


section CertificatePort132
section
namespace Enclosure
noncomputable def sfrac (neg : Bool) (cn cd : ℕ) : ℝ := (if neg then -1 else 1) * ((cn : ℝ) / cd)
theorem sfrac_not (neg : Bool) (cn cd : ℕ) : sfrac (!neg) cn cd = - sfrac neg cn cd := by
  cases neg <;> simp [sfrac]
theorem sfrac_false_div (cn cd : ℕ) : sfrac false cn cd = (cn : ℝ) / cd := by simp [sfrac]
















theorem pos_of_ble {n : ℕ} (h : Nat.ble 1 n = true) : 0 < n :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_ble_eq_true h)
theorem pos_real_of_ble {n : ℕ} (h : Nat.ble 1 n = true) : (0 : ℝ) < n := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_ble_eq_true h)














end Enclosure
end
end CertificatePort132


section CertificatePort133
section
namespace Zeta.Certificates








namespace BatchSpec
variable {n an ad bn bd : ℕ}








end BatchSpec


























end Zeta.Certificates
end
end CertificatePort133


section CertificatePort134
section
open Set
open scoped ComplexConjugate










end
end CertificatePort134


section CertificatePort135
section
open scoped Nat
namespace TangentNumbers
noncomputable section
section Poly
open Polynomial










open Complex


end Poly
section PowerSeries
open PowerSeries
section ForMathlib




end ForMathlib












open scoped Polynomial












section
variable {R : Type*} [Semiring R] {p : R⟦X⟧}








end




end PowerSeries
end
end TangentNumbers
end
end CertificatePort135






section CertificatePort138
section
open scoped Nat
namespace TangentNumbers










end TangentNumbers
end
end CertificatePort138


section CertificatePort139
section
namespace BSN
def binarySplit (p q : Nat → Nat) (m n : Nat) : Nat × Nat × Nat :=
  if _h : m < n then
    if _h2 : m + 1 = n then (p m, q m, p m)
    else
      let (tl, ql, pl) := binarySplit p q m ((m + n) / 2)
      let (tr, qr, pr) := binarySplit p q ((m + n) / 2) n
      (tl * qr + pl * tr, ql * qr, pl * pr)
  else (0, 1, 1)
termination_by n - m
decreasing_by all_goals omega
def cosEvenP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def cosEvenQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.succ (Nat.mul 4 k)) (Nat.add (Nat.mul 4 k) 2))
      (Nat.add (Nat.mul 4 k) 3)) (Nat.add (Nat.mul 4 k) 4))
def cosOddP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def cosOddQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 3) (Nat.add (Nat.mul 4 k) 4))
      (Nat.add (Nat.mul 4 k) 5)) (Nat.add (Nat.mul 4 k) 6))
def sinEvenP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def sinEvenQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 2) (Nat.add (Nat.mul 4 k) 3))
      (Nat.add (Nat.mul 4 k) 4)) (Nat.add (Nat.mul 4 k) 5))
def sinOddP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def sinOddQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 4) (Nat.add (Nat.mul 4 k) 5))
      (Nat.add (Nat.mul 4 k) 6)) (Nat.add (Nat.mul 4 k) 7))
def artanhP (u : Nat) : Nat
    → Nat := fun k => Nat.mul (Nat.pow u (nat_lit 2)) (Nat.succ (Nat.mul (nat_lit 2) k))
def artanhQ (v : Nat) : Nat
    → Nat := fun k => Nat.mul (Nat.pow v (nat_lit 2)) (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 3))
def arctanEvenP (u : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow u 4) (Nat.succ (Nat.mul 4 k))
def arctanEvenQ (v : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow v 4) (Nat.add (Nat.mul 4 k) 5)
def arctanOddP (u : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow u 4) (Nat.add (Nat.mul 4 k) 3)
def arctanOddQ (v : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow v 4) (Nat.add (Nat.mul 4 k) 7)
end BSN
end
end CertificatePort139


section CertificatePort140
section
namespace BSN
open Enclosure
open Finset
theorem binarySplit_PQ {p q : ℕ → ℕ} {m n : ℕ} :
    (binarySplit p q m n).2.2 = ∏ j ∈ Ico m n, p j ∧
    (binarySplit p q m n).2.1 = ∏ j ∈ Ico m n, q j := by
  fun_induction binarySplit with
  | case1 m hlt => simp [Nat.Ico_succ_singleton]
  | case3 m n => simp_all
  | case2 m n hlt hne tl ql pl hL tr qr pr hR ihL ihR =>
    simp only [hL] at ihL; simp only [hR] at ihR
    have hmk : m ≤ (m + n) / 2 := by omega
    have hkn : (m + n) / 2 ≤ n := by omega
    refine ⟨?_, ?_⟩ <;>
      rw [← prod_Ico_consecutive _ hmk hkn] <;> simp [ihL.1, ihL.2, ihR.1, ihR.2]
theorem binarySplit_nonzero {p q : ℕ → ℕ} {m n : ℕ} (hq : ∀ i, q i ≠ 0) :
    (binarySplit p q m n).2.1 ≠ 0 := by
  fun_induction binarySplit <;> simp_all
theorem binarySplit_spec {p q : ℕ → ℕ} {m n T Q P : ℕ} (hq : ∀ i, q i ≠ 0)
    (h : (T, Q, P) = binarySplit p q m n) :
    (∏ j ∈ Ico m n, ((p j : ℚ) / q j) = (P : ℚ) / Q) ∧
    (∑ i ∈ Ico m n, ∏ j ∈ Ico m (i + 1), ((p j : ℚ) / q j) = (T : ℚ) / Q) := by
  fun_induction binarySplit generalizing T Q P with
  | case1 m hlt =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hIco : Finset.Ico m (m + 1) = {m} := by
      ext x; rw [Finset.mem_Ico, Finset.mem_singleton]; omega
    simp [hIco]
  | case3 m n =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Ico_eq_empty (by omega : ¬ m < n)]
  | case2 m n hlt hne tl ql pl hL tr qr pr hR ihL ihR =>
    specialize ihL hL.symm; specialize ihR hR.symm
    have hmk : m ≤ (m + n) / 2 := by omega
    have hkn : (m + n) / 2 ≤ n := by omega
    obtain ⟨hPl, hSl⟩ := ihL
    obtain ⟨hPr, hSr⟩ := ihR
    obtain ⟨hPpl, hQl⟩ := (binarySplit_PQ (p := p) (q := q) (m := m) (n := (m + n) / 2))
    simp only [hL] at hPpl hQl
    obtain ⟨hPpr, hQr⟩ := (binarySplit_PQ (p := p) (q := q) (m := (m + n) / 2) (n := n))
    simp only [hR] at hPpr hQr
    have hqtl := binarySplit_nonzero (p := p) (m := m) (n := (m + n) / 2) hq
    simp only [hL] at hqtl
    have hqtr := binarySplit_nonzero (p := p) (m := (m + n) / 2) (n := n) hq
    simp only [hR] at hqtr
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hqlr : (ql : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqtl
    have hqrr : (qr : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqtr
    constructor
    · rw [← prod_Ico_consecutive _ hmk hkn, hPl, hPr]; push_cast; field_simp
    · rw [← sum_Ico_consecutive _ hmk hkn, hSl]
      have hsplit : ∑ i ∈ Ico ((m + n) / 2) n, ∏ j ∈ Ico m (i + 1), ((p j : ℚ) / q j)
          = ((pl : ℚ) / ql) * ∑ i ∈ Ico ((m + n) / 2) n, ∏ j ∈ Ico ((m + n) / 2) (i + 1),
              ((p j : ℚ) / q j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_Ico] at hi
        rw [← prod_Ico_consecutive _ hmk (by omega : (m + n) / 2 ≤ i + 1), hPl]
      rw [hsplit, hSr]
      push_cast
      field_simp
theorem Nat.div_eq' {a b : ℕ} : a.div b = a / b := rfl
theorem binarySplit_of_le {p q : ℕ → ℕ} {m n : ℕ} (h : n.ble m) :
    binarySplit p q m n = (0, 1, 1) := by
  rw [binarySplit]; simp only [Nat.ble_eq] at h; rw [dif_neg (by omega)]
theorem binarySplit_of_base {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.succ).beq n) (hT : T.beq (p m)) (hQ : Q.beq (q m)) (hP : P.beq (p m)) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  rw [binarySplit, dif_pos (by omega), dif_pos rfl]
theorem binarySplit_rec {p q : ℕ → ℕ}
    {m n k tl ql pl tr qr pr T Q P : ℕ}
    (h1 : (m.succ).blt n) (hk : k.beq ((m.add n).div 2))
    (hT : T.beq ((tl.mul qr).add (pl.mul tr))) (hQ : Q.beq (ql.mul qr))
    (hP : P.beq (pl.mul pr))
    (hl : binarySplit p q m k = (tl, ql, pl))
    (hr : binarySplit p q k n = (tr, qr, pr)) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.div_eq'] at h1 hk hT hQ hP
  subst hk hT hQ hP
  rw [binarySplit, dif_pos (by omega), dif_neg (by omega), hl, hr]
theorem binarySplit_of_base2 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 2).beq n)
    (hT : T.beq (((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))))
    (hQ : Q.beq ((q m).mul (q (m.succ))))
    (hP : P.beq ((p m).mul (p (m.succ)))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 1) = (p m, q m, p m) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  have hr : binarySplit p q (m + 1) (m + 2) = (p (m + 1), q (m + 1), p (m + 1)) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base3 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 3).beq n)
    (hT : T.beq (((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add
      ((p m).mul (((p (m.succ)).mul (q (m.add 2))).add
        ((p (m.succ)).mul (p (m.add 2)))))))
    (hQ : Q.beq ((q m).mul ((q (m.succ)).mul (q (m.add 2)))))
    (hP : P.beq ((p m).mul ((p (m.succ)).mul (p (m.add 2))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 1) = (p m, q m, p m) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  have hr : binarySplit p q (m + 1) (m + 3) =
      (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2), q (m + 1) * q (m + 2),
        p (m + 1) * p (m + 2)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base4 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 4).beq n)
    (hT : T.beq (((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul
        ((q (m.add 2)).mul (q (m.add 3)))).add
      (((p m).mul (p (m.succ))).mul
        (((p (m.add 2)).mul (q (m.add 3))).add ((p (m.add 2)).mul (p (m.add 3)))))))
    (hQ : Q.beq (((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))))
    (hP : P.beq (((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 2) =
      (p m * q (m + 1) + p m * p (m + 1), q m * q (m + 1), p m * p (m + 1)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 2) (m + 4) =
      (p (m + 2) * q (m + 3) + p (m + 2) * p (m + 3), q (m + 2) * q (m + 3),
        p (m + 2) * p (m + 3)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base5 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 5).beq n)
    (hT : T.beq (((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add 2)).mul
        ((q (m.add 3)).mul (q (m.add 4))))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul
        ((q (m.add 3)).mul (q (m.add 4)))).add ((p (m.add 2)).mul (((p (m.add 3)).mul (q (m.add
        4))).add ((p (m.add 3)).mul (p (m.add 4)))))))))
    (hQ : Q.beq (((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul ((q (m.add 3)).mul (q (m.add
        4))))))
    (hP : P.beq (((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add
        4)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 2) =
      (p m * q (m + 1) + p m * p (m + 1), q m * q (m + 1), p m * p (m + 1)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 2) (m + 5) =
      (p (m + 2) * (q (m + 3) * q (m + 4)) + p (m + 2) * (p (m + 3) * q (m + 4) + p (m + 3) * p (m
          + 4)), q (m + 2) * (q (m + 3) * q (m + 4)), p (m + 2) * (p (m + 3) * p (m + 4))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base6 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 6).beq n)
    (hT : T.beq (((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5)))))))))
    (hQ : Q.beq (((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))))
    (hP : P.beq (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 3) =
      (p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2)), q m
          * (q (m + 1) * q (m + 2)), p m * (p (m + 1) * p (m + 2))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 3) (m + 6) =
      (p (m + 3) * (q (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m
          + 5)), q (m + 3) * (q (m + 4) * q (m + 5)), p (m + 3) * (p (m + 4) * p (m + 5))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base7 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 7).beq n)
    (hT : T.beq (((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul (((q (m.add 3)).mul (q
        (m.add 4))).mul ((q (m.add 5)).mul (q (m.add 6))))).add (((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((((p (m.add 3)).mul (q (m.add 4))).add ((p (m.add 3)).mul (p (m.add
        4)))).mul ((q (m.add 5)).mul (q (m.add 6)))).add (((p (m.add 3)).mul (p (m.add 4))).mul
        (((p (m.add 5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))))))))
    (hQ : Q.beq (((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul (((q (m.add 3)).mul (q (m.add
        4))).mul ((q (m.add 5)).mul (q (m.add 6))))))
    (hP : P.beq (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add
        4))).mul ((p (m.add 5)).mul (p (m.add 6)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 3) =
      (p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2)), q m
          * (q (m + 1) * q (m + 2)), p m * (p (m + 1) * p (m + 2))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 3) (m + 7) =
      ((p (m + 3) * q (m + 4) + p (m + 3) * p (m + 4)) * (q (m + 5) * q (m + 6)) + p (m + 3) * p
          (m + 4) * (p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6)), q (m + 3) * q (m + 4) * (q (m
          + 5) * q (m + 6)), p (m + 3) * p (m + 4) * (p (m + 5) * p (m + 6))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base8 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 8).beq n)
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul (q (m.add 7))))).add ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul
        (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add
        5)))).mul ((q (m.add 6)).mul (q (m.add 7)))).add (((p (m.add 4)).mul (p (m.add 5))).mul
        (((p (m.add 6)).mul (q (m.add 7))).add ((p (m.add 6)).mul (p (m.add 7)))))))))
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q (m.add
        4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul (q (m.add 7))))))
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add
        4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul (p (m.add 7)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 4) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3)), q m * q (m + 1) * (q (m + 2) * q (m + 3)), p m
          * p (m + 1) * (p (m + 2) * p (m + 3))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 4) (m + 8) =
      ((p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5)) * (q (m + 6) * q (m + 7)) + p (m + 4) * p
          (m + 5) * (p (m + 6) * q (m + 7) + p (m + 6) * p (m + 7)), q (m + 4) * q (m + 5) * (q (m
          + 6) * q (m + 7)), p (m + 4) * p (m + 5) * (p (m + 6) * p (m + 7))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr
theorem binarySplit_of_base9 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 9).beq n)
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))))).add ((((p m).mul (p (m.add
        1))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add
        ((p (m.add 4)).mul (p (m.add 5)))).mul ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add
        8))))).add (((p (m.add 4)).mul (p (m.add 5))).mul (((p (m.add 6)).mul ((q (m.add 7)).mul
        (q (m.add 8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p (m.add
        7)).mul (p (m.add 8)))))))))))
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q (m.add
        4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))))))
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add
        4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 4) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3)), q m * q (m + 1) * (q (m + 2) * q (m + 3)), p m
          * p (m + 1) * (p (m + 2) * p (m + 3))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 4) (m + 9) =
      ((p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5)) * (q (m + 6) * (q (m + 7) * q (m + 8))) + p
          (m + 4) * p (m + 5) * (p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q
          (m + 8) + p (m + 7) * p (m + 8))), q (m + 4) * q (m + 5) * (q (m + 6) * (q (m + 7) * q
          (m + 8))), p (m + 4) * p (m + 5) * (p (m + 6) * (p (m + 7) * p (m + 8)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr






theorem binarySplit_of_base13 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 13).beq n)
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5)))))))).mul (((q (m.add 6)).mul
        ((q (m.add 7)).mul (q (m.add 8)))).mul (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add
        11)).mul (q (m.add 12)))))).add ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p
        (m.add 3)).mul ((p (m.add 4)).mul (p (m.add 5))))).mul (((((p (m.add 6)).mul ((q (m.add
        7)).mul (q (m.add 8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p
        (m.add 7)).mul (p (m.add 8)))))).mul (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add
        11)).mul (q (m.add 12))))).add (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        (((((p (m.add 9)).mul (q (m.add 10))).add ((p (m.add 9)).mul (p (m.add 10)))).mul ((q
        (m.add 11)).mul (q (m.add 12)))).add (((p (m.add 9)).mul (p (m.add 10))).mul (((p (m.add
        11)).mul (q (m.add 12))).add ((p (m.add 11)).mul (p (m.add 12)))))))))))
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))).mul (((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))).mul
        (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add 11)).mul (q (m.add 12)))))))
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5))))).mul (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        (((p (m.add 9)).mul (p (m.add 10))).mul ((p (m.add 11)).mul (p (m.add 12))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 6) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * (q (m + 4) * q (m + 5))) + p m * (p (m + 1) * p (m + 2)) * (p (m + 3) * (q
          (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5))), q m
          * (q (m + 1) * q (m + 2)) * (q (m + 3) * (q (m + 4) * q (m + 5))), p m * (p (m + 1) * p
          (m + 2)) * (p (m + 3) * (p (m + 4) * p (m + 5)))) :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 6) (m + 13) =
      ((p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q (m + 8) + p (m + 7) * p
          (m + 8))) * (q (m + 9) * q (m + 10) * (q (m + 11) * q (m + 12))) + p (m + 6) * (p (m +
          7) * p (m + 8)) * ((p (m + 9) * q (m + 10) + p (m + 9) * p (m + 10)) * (q (m + 11) * q
          (m + 12)) + p (m + 9) * p (m + 10) * (p (m + 11) * q (m + 12) + p (m + 11) * p (m +
          12))), q (m + 6) * (q (m + 7) * q (m + 8)) * (q (m + 9) * q (m + 10) * (q (m + 11) * q
          (m + 12))), p (m + 6) * (p (m + 7) * p (m + 8)) * (p (m + 9) * p (m + 10) * (p (m + 11)
          * p (m + 12)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr






end BSN
end
end CertificatePort140


section CertificatePort141
section
namespace BSN
open Enclosure
open TangentNumbers




end BSN
end
end CertificatePort141






section CertificatePort142
section
namespace Enclosure
def numPos (neg : Bool) (cn : Nat) : Nat := if neg then 0 else cn
def numNeg (neg : Bool) (cn : Nat) : Nat := if neg then cn else 0
def recentreOk (cn cd rn rd cn' cd' rn' rd' : Nat) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cd)
    (Nat.add (Nat.sub (nat_lit 1) cd')
    (Nat.add (Nat.sub (nat_lit 1) rd)
    (Nat.add (Nat.sub (nat_lit 1) rd')
    (Nat.add (Nat.sub (cn'.mul cd) (cn.mul cd'))
             (Nat.sub (((rn.mul (cd.mul cd')).add (((cn.mul cd').sub (cn'.mul cd)).mul rd)).mul rd')
                      (rn'.mul (rd.mul (cd.mul cd')))))))))
    (nat_lit 0)
end Enclosure
end
end CertificatePort142


section CertificatePort143
section
namespace Enclosure
def Real.IsNear (x : ℝ) (neg : Bool) (cn cd rn rd : ℕ) : Prop :=
  |x - sfrac neg cn cd| ≤ (rn : ℝ) / rd
theorem Real.IsNear.lower {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (h : Real.IsNear x neg cn cd rn rd) : sfrac neg cn cd - (rn : ℝ) / rd ≤ x := by
  have := (abs_le.mp h).1; linarith
theorem Real.IsNear.upper {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (h : Real.IsNear x neg cn cd rn rd) : x ≤ sfrac neg cn cd + (rn : ℝ) / rd := by
  have := (abs_le.mp h).2; linarith


theorem sfrac_eq_parts (neg : Bool) (cn cd : ℕ) :
    sfrac neg cn cd = ((numPos neg cn : ℝ) - (numNeg neg cn : ℝ)) / cd := by
  cases neg <;> simp [sfrac, numPos, numNeg, neg_div, sub_zero, zero_sub]
theorem abs_sfrac (neg : Bool) (cn cd : ℕ) : |sfrac neg cn cd| = (cn : ℝ) / cd := by
  rw [sfrac]
  cases neg <;> simp [abs_div, abs_of_nonneg]
theorem sfrac_mul (nx ny : Bool) (cnx cdx cny cdy : ℕ) :
    sfrac nx cnx cdx * sfrac ny cny cdy = sfrac (Bool.xor nx ny) (cnx * cny) (cdx * cdy) := by
  cases nx <;> cases ny <;> simp [sfrac] <;> ring
theorem Real.IsNear.const (neg : Bool) (cn cd : ℕ) :
    Real.IsNear (sfrac neg cn cd) neg cn cd (nat_lit 0) (nat_lit 1) := by
  simp [Real.IsNear]


end Enclosure
end
end CertificatePort143


section CertificatePort144
section
namespace Enclosure
theorem Real.IsNear.add {x y : ℝ} {nx ny nR : Bool} {cnx cdx rnx rdx cny cdy rny rdy cnR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg ny cny).mul cdx))
                    (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add
                          ((numPos ny cny).mul cdx))) :
    Real.IsNear (x + y) nR cnR (cdx.mul cdy) ((rnx.mul rdy).add (rny.mul rdx)) (rdx.mul rdy) := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hcdyR : (0:ℝ) < cdy := pos_real_of_ble hcdy
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hrdyR : (0:ℝ) < rdy := pos_real_of_ble hrdy
  have eR : (numPos nR cnR : ℝ) + (numNeg nx cnx : ℝ) * cdy + (numNeg ny cny : ℝ) * cdx
          = (numNeg nR cnR : ℝ) + (numPos nx cnx : ℝ) * cdy + (numPos ny cny : ℝ) * cdx := by
    have h' := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.add_eq, Nat.mul_eq] at h'
    exact_mod_cast h'
  have hc : sfrac nR cnR (cdx * cdy) = sfrac nx cnx cdx + sfrac ny cny cdy := by
    rw [sfrac_eq_parts nR cnR, sfrac_eq_parts nx cnx, sfrac_eq_parts ny cny,
      div_add_div _ _ (ne_of_gt hcdxR) (ne_of_gt hcdyR), Nat.cast_mul,
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (cdx : ℝ) * (cdy : ℝ) * eR
  have hrad : ((rnx * rdy + rny * rdx : ℕ) : ℝ) / ((rdx * rdy : ℕ) : ℝ)
            = (rnx : ℝ) / rdx + (rny : ℝ) / rdy := by
    rw [div_add_div _ _ (ne_of_gt hrdxR) (ne_of_gt hrdyR)]
    push_cast
    ring
  simp only [Real.IsNear] at hx hy ⊢
  rw [hc, hrad]
  calc |x + y - (sfrac nx cnx cdx + sfrac ny cny cdy)|
      = |(x - sfrac nx cnx cdx) + (y - sfrac ny cny cdy)| := by congr 1; ring
    _ ≤ |x - sfrac nx cnx cdx| + |y - sfrac ny cny cdy| := abs_add_le _ _
    _ ≤ (rnx : ℝ) / rdx + (rny : ℝ) / rdy := add_le_add hx hy
theorem Real.IsNear.neg {x : ℝ} {nx : Bool} {cnx cdx rnx rdx : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) : Real.IsNear (-x) (!nx) cnx cdx rnx rdx := by
  simp only [Real.IsNear, sfrac_not] at hx ⊢
  have : -x - -sfrac nx cnx cdx = -(x - sfrac nx cnx cdx) := by ring
  rwa [this, abs_neg]


theorem abs_mul_sub {x y cx cy rx ry : ℝ} (hx : |x - cx| ≤ rx) (hy : |y - cy| ≤ ry) :
    |x * y - cx * cy| ≤ |cx| * ry + |cy| * rx + rx * ry := by
  have hrx : 0 ≤ rx := le_trans (abs_nonneg _) hx
  calc |x * y - cx * cy|
      = |cx * (y - cy) + cy * (x - cx) + (x - cx) * (y - cy)| := by congr 1; ring
    _ ≤ |cx * (y - cy) + cy * (x - cx)| + |(x - cx) * (y - cy)| := abs_add_le _ _
    _ ≤ (|cx * (y - cy)| + |cy * (x - cx)|) + |(x - cx) * (y - cy)| := by
        gcongr; exact abs_add_le _ _
    _ = |cx| * |y - cy| + |cy| * |x - cx| + |x - cx| * |y - cy| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |cx| * ry + |cy| * rx + rx * ry := by gcongr
theorem Real.IsNear.mul {x y : ℝ} {nx ny : Bool} {cnx cdx rnx rdx cny cdy rny rdy : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy) :
    Real.IsNear (x * y) (Bool.xor nx ny) (cnx.mul cny) (cdx.mul cdy)
      (((((cnx.mul rny).mul cdy).mul rdx).add (((cny.mul rnx).mul cdx).mul rdy)).add
        (((rnx.mul rny).mul cdx).mul cdy))
      (((cdx.mul cdy).mul rdx).mul rdy) := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hcdyR : (0:ℝ) < cdy := pos_real_of_ble hcdy
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hrdyR : (0:ℝ) < rdy := pos_real_of_ble hrdy
  have hcdxN : 0 < cdx := pos_of_ble hcdx
  have hcdyN : 0 < cdy := pos_of_ble hcdy
  have hrdxN : 0 < rdx := pos_of_ble hrdx
  have hrdyN : 0 < rdy := pos_of_ble hrdy
  have hrad : (cnx : ℝ) / cdx * ((rny : ℝ) / rdy) + (cny : ℝ) / cdy * ((rnx : ℝ) / rdx)
              + (rnx : ℝ) / rdx * ((rny : ℝ) / rdy)
            = ((cnx * rny * cdy * rdx + cny * rnx * cdx * rdy + rnx * rny * cdx * cdy : ℕ) : ℝ)
              / ((cdx * cdy * rdx * rdy : ℕ) : ℝ) := by
    rw [eq_div_iff (by positivity)]
    push_cast
    field_simp
  simp only [Real.IsNear] at hx hy ⊢
  rw [← sfrac_mul]
  refine le_trans (abs_mul_sub hx hy) ?_
  rw [abs_sfrac, abs_sfrac, hrad]
private theorem ble_one_mul {a b : ℕ} (ha : Nat.ble (nat_lit 1) a
      = true) (hb : Nat.ble (nat_lit 1) b = true) :
    Nat.ble (nat_lit 1) (a.mul b) = true := by
  rw [Nat.ble_eq] at ha hb ⊢
  have h := Nat.mul_le_mul ha hb
  omega
theorem Real.IsNear.reprLit {x : ℝ} {n : Bool} {cn D Rn Rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn D Rn Rd)
    (hD : Nat.ble (nat_lit 1) D) (hRd : Nat.ble (nat_lit 1) Rd) (hcd' : Nat.ble (nat_lit 1)
          cd') (hrd' : Nat.ble (nat_lit 1) rd')
    (hc : Nat.beq (cn.mul cd') (cn'.mul D))
    (hr : Nat.ble (Rn.mul rd') (rn'.mul Rd)) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [Nat.ble_eq, Nat.mul_eq] at hr
  have hDr : (0:ℝ) < D := pos_real_of_ble hD
  have hRdr : (0:ℝ) < Rd := pos_real_of_ble hRd
  have hcd'r : (0:ℝ) < cd' := pos_real_of_ble hcd'
  have hrd'r : (0:ℝ) < rd' := pos_real_of_ble hrd'
  have hceq : (cn : ℝ) / D = (cn' : ℝ) / cd' := by
    have hc' := Nat.eq_of_beq_eq_true hc
    simp only [Nat.mul_eq] at hc'
    rw [div_eq_div_iff hDr.ne' hcd'r.ne']; exact_mod_cast hc'
  have hsfrac : sfrac n cn D = sfrac n cn' cd' := by simp only [sfrac, hceq]
  have hrle : (Rn : ℝ) / Rd ≤ (rn' : ℝ) / rd' := by
    rw [div_le_div_iff₀ hRdr hrd'r]; exact_mod_cast hr
  simp only [Real.IsNear] at h ⊢
  rw [← hsfrac]
  exact le_trans h hrle
theorem Real.IsNear.addLit {x y : ℝ} {nx ny nR : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg ny cny).mul cdx))
                    (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add ((numPos ny cny).mul cdx)))
    (hcdR' : Nat.ble (nat_lit 1) cdR') (hrdR' : Nat.ble (nat_lit 1) rdR')
    (hc : Nat.beq (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)))
    (hr : Nat.ble (((rnx.mul rdy).add (rny.mul rdx)).mul rdR') (rnR'.mul (rdx.mul rdy))) :
    Real.IsNear (x + y) nR cnR' cdR' rnR' rdR' :=
  (hx.add hy hcdx hcdy hrdx hrdy hnum).reprLit
    (ble_one_mul hcdx hcdy) (ble_one_mul hrdx hrdy) hcdR' hrdR' hc hr


private theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  simpa [Nat.beq_eq_true_eq] using h




def mulLitOk (cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cdx)
    (Nat.add (Nat.sub (nat_lit 1) cdy)
    (Nat.add (Nat.sub (nat_lit 1) rdx)
    (Nat.add (Nat.sub (nat_lit 1) rdy)
    (Nat.add (Nat.sub (nat_lit 1) cdR)
    (Nat.add (Nat.sub (nat_lit 1) rdR)
    (Nat.add (Nat.sub ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)))
    (Nat.add (Nat.sub (cnR.mul (cdx.mul cdy)) ((cnx.mul cny).mul cdR))
             (Nat.sub ((((((cnx.mul rny).mul cdy).mul rdx).add
                         (((cny.mul rnx).mul cdx).mul rdy)).add
                         (((rnx.mul rny).mul cdx).mul cdy)).mul rdR)
                      (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy)))))))))))
    (nat_lit 0)
private theorem mulLitOk_parts {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Nat.ble (nat_lit 1) cdx = true ∧ Nat.ble (nat_lit 1) cdy = true ∧
    Nat.ble (nat_lit 1) rdx = true ∧ Nat.ble (nat_lit 1) rdy = true ∧
    Nat.ble (nat_lit 1) cdR = true ∧ Nat.ble (nat_lit 1) rdR = true ∧
    Nat.beq ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)) = true ∧
    Nat.ble ((((((cnx.mul rny).mul cdy).mul rdx).add (((cny.mul rnx).mul cdx).mul rdy)).add
      (((rnx.mul rny).mul cdx).mul cdy)).mul rdR) (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy))
      = true := by
  simp only [mulLitOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z6, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z7, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z8, z9⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6),
    beq_of_eq (Nat.le_antisymm (Nat.le_of_sub_eq_zero z7) (Nat.le_of_sub_eq_zero z8)),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z9)⟩
























theorem Real.IsNear.mulLit {x y : ℝ} {nx ny : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hcdR : Nat.ble (nat_lit 1) cdR) (hrdR : Nat.ble (nat_lit 1) rdR)
    (hc : Nat.beq ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)))
    (hr : Nat.ble (((((((cnx.mul rny).mul cdy).mul rdx).add
        (((cny.mul rnx).mul cdx).mul rdy)).add (((rnx.mul rny).mul cdx).mul cdy)).mul rdR))
      (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy))) :
    Real.IsNear (x * y) (Bool.xor nx ny) cnR cdR rnR rdR :=
  (hx.mul hy hcdx hcdy hrdx hrdy).reprLit (ble_one_mul hcdx hcdy)
    (ble_one_mul (ble_one_mul (ble_one_mul hcdx hcdy) hrdx) hrdy) hcdR hrdR hc hr
theorem Real.IsNear.mulLit_ff {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) false cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr
theorem Real.IsNear.mulLit_ft {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) true cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr




theorem Real.IsNear.recentre {x : ℝ} {n : Bool} {cn cd rn rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd)
    (hcd : Nat.ble (nat_lit 1) cd) (hcd' : Nat.ble (nat_lit 1) cd') (hrd : Nat.ble (nat_lit 1)
          rd) (hrd' : Nat.ble (nat_lit 1) rd')
    (hfloor : Nat.ble (cn'.mul cd) (cn.mul cd'))
    (hrad : Nat.ble (((rn.mul (cd.mul cd')).add (((cn.mul cd').sub (cn'.mul cd)).mul rd)).mul rd')
                    (rn'.mul (rd.mul (cd.mul cd')))) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hfloor hrad
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hcd'R : (0:ℝ) < cd' := pos_real_of_ble hcd'
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hrd'R : (0:ℝ) < rd' := pos_real_of_ble hrd'
  have hnn : (0:ℝ) ≤ (cn : ℝ) / cd - (cn' : ℝ) / cd' := by
    have : (cn' : ℝ) / cd' ≤ (cn : ℝ) / cd := by
      rw [div_le_div_iff₀ hcd'R hcdR]; exact_mod_cast hfloor
    linarith
  have hmagdiff : |sfrac n cn cd - sfrac n cn' cd'| = (cn : ℝ) / cd - (cn' : ℝ) / cd' := by
    have hsdiff : sfrac n cn cd - sfrac n cn' cd'
        = (if n then -1 else 1) * ((cn : ℝ) / cd - (cn' : ℝ) / cd') := by
      simp only [sfrac]; ring
    rw [hsdiff, abs_mul]; cases n <;> simp [abs_of_nonneg hnn]
  have hkey : (rn : ℝ) / rd + ((cn : ℝ) / cd - (cn' : ℝ) / cd') ≤ (rn' : ℝ) / rd' := by
    rw [div_sub_div _ _ (ne_of_gt hcdR) (ne_of_gt hcd'R),
      div_add_div _ _ (ne_of_gt hrdR) (by positivity), div_le_div_iff₀ (by positivity) hrd'R]
    have hcast : ((cn : ℝ) * cd' - cd * cn') = ((cn * cd' - cn' * cd : ℕ) : ℝ) := by
      rw [Nat.cast_sub hfloor]; push_cast; ring
    rw [hcast]
    have h2 : (((rn * (cd * cd') + (cn * cd' - cn' * cd) * rd) * rd' : ℕ) : ℝ)
            ≤ ((rn' * (rd * (cd * cd')) : ℕ) : ℝ) := by exact_mod_cast hrad
    push_cast at h2 ⊢
    nlinarith [h2]
  simp only [Real.IsNear] at h ⊢
  calc |x - sfrac n cn' cd'|
      ≤ |x - sfrac n cn cd| + |sfrac n cn cd - sfrac n cn' cd'| := abs_sub_le _ _ _
    _ ≤ (rn : ℝ) / rd + ((cn : ℝ) / cd - (cn' : ℝ) / cd') := by
      rw [hmagdiff]; exact add_le_add h le_rfl
    _ ≤ (rn' : ℝ) / rd' := hkey
theorem Real.IsNear.recentre' {x : ℝ} {n : Bool} {cn cd rn rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd)
    (hs : recentreOk cn cd rn rd cn' cd' rn' rd' = true) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [recentreOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, z6⟩ := Nat.add_eq_zero_iff.mp hs
  exact Real.IsNear.recentre h
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2))
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4))
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6))
end Enclosure
end
end CertificatePort144


section CertificatePort145
section
namespace Enclosure
theorem Real.IsNear.lipschitz_image {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y|)
    {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (f c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (f x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) := by
  subst hc
  simp only [Nat.mul_eq, Nat.add_eq]
  have hρdR : (0:ℝ) < ρd := pos_real_of_ble hρd
  have hrsdR : (0:ℝ) < rsd := pos_real_of_ble hrsd
  have hρdN : 0 < ρd := pos_of_ble hρd
  have hrsdN : 0 < rsd := pos_of_ble hrsd
  simp only [Real.IsNear] at hx hsc ⊢
  have hrad : ((rsn * ρd + ρn * rsd : ℕ) : ℝ) / ((rsd * ρd : ℕ) : ℝ)
            = (ρn : ℝ) / ρd + (rsn : ℝ) / rsd := by
    rw [div_eq_iff (by positivity)]; push_cast; field_simp; ring
  rw [hrad]
  calc |f x - sfrac sn scn scd|
      ≤ |f x - f (sfrac nc cn cd)| + |f (sfrac nc cn cd) - sfrac sn scn scd| :=
        abs_sub_le _ _ _
    _ ≤ |x - sfrac nc cn cd| + (rsn : ℝ) / rsd := add_le_add (hf _ _) hsc
    _ ≤ (ρn : ℝ) / ρd + (rsn : ℝ) / rsd := by linarith [hx]
theorem Real.IsNear.sin_image {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (Real.sin c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (Real.sin x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) :=
  lipschitz_image (fun _ _ => Real.abs_sin_sub_sin_le _ _) hx hc hsc hρd hrsd
theorem Real.IsNear.cos_image {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (Real.cos c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (Real.cos x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) :=
  lipschitz_image (fun _ _ => Real.abs_cos_sub_cos_le _ _) hx hc hsc hρd hrsd
theorem Real.IsNear.of_endpoints {z : ℝ} {a b Q : ℕ} (hQ : Nat.ble 1 Q)
    (h1 : (a : ℝ) / Q ≤ z) (h2 : z ≤ (b : ℝ) / Q) :
    Real.IsNear z false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a) (Nat.mul (nat_lit 2) Q) := by
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hab : a ≤ b := by
    have hh : (a : ℝ) / Q ≤ (b : ℝ) / Q := le_trans h1 h2
    rw [div_le_div_iff₀ hQR hQR] at hh
    exact_mod_cast le_of_mul_le_mul_right hh hQR
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  have hc1 : ((a : ℝ) + b) / (2 * Q) - ((b : ℝ) - a) / (2 * Q) = (a : ℝ) / Q := by field_simp; ring
  have hc2 : ((a : ℝ) + b) / (2 * Q) + ((b : ℝ) - a) / (2 * Q) = (b : ℝ) / Q := by field_simp; ring
  rw [Real.IsNear, sfrac_false_div, abs_le]
  push_cast [hcast]
  exact ⟨by linarith [h1, hc1], by linarith [h2, hc2]⟩




theorem Real.IsNear.inv_image {x : ℝ} {cn cd rn rd a b Q : ℕ}
    (hx : Real.IsNear x false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hQ : Nat.ble 1 Q)
    (hpos : Nat.blt (rn.mul cd) (cn.mul rd))
    (hlo : Nat.ble (a.mul ((cn.mul rd).add (rn.mul cd))) (Q.mul (cd.mul rd)))
    (hhi : Nat.ble (Q.mul (cd.mul rd)) (b.mul ((cn.mul rd).sub (rn.mul cd)))) :
    Real.IsNear x⁻¹ false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a)
      (Nat.mul (nat_lit 2) Q) := by
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hpos hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hposn : rn * cd < cn * rd := hpos
  have hsub : ((cn * rd - rn * cd : ℕ) : ℝ) = (cn : ℝ) * rd - rn * cd := by
    rw [Nat.cast_sub hposn.le]; push_cast; ring
  have hloQ : (0:ℝ) < (cn : ℝ) / cd - (rn : ℝ) / rd := by
    rw [div_sub_div _ _ hcdR.ne' hrdR.ne', lt_div_iff₀ (by positivity)]
    have h := hposn
    have : ((rn * cd : ℕ) : ℝ) < ((cn * rd : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; nlinarith [this]
  have hSlo : (cn : ℝ) / cd - (rn : ℝ) / rd ≤ x := by
    have h := hx.lower; rwa [sfrac_false_div] at h
  have hShi : x ≤ (cn : ℝ) / cd + (rn : ℝ) / rd := by
    have h := hx.upper; rwa [sfrac_false_div] at h
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le hloQ hSlo
  have hdiffR : (0:ℝ) < (cn : ℝ) * rd - (cd : ℝ) * rn := by
    have h' : ((rn * cd : ℕ) : ℝ) < ((cn * rd : ℕ) : ℝ) := by exact_mod_cast hposn
    push_cast at h'; linarith
  have hsumR : (0:ℝ) < (cn : ℝ) * rd + (cd : ℝ) * rn := by
    have hcdrn : (0:ℝ) ≤ (cd : ℝ) * rn := by positivity
    linarith
  have h1 : (a : ℝ) / Q ≤ x⁻¹ := by
    have hstep : (a : ℝ) / Q ≤ ((cn : ℝ) / cd + (rn : ℝ) / rd)⁻¹ := by
      rw [div_add_div _ _ hcdR.ne' hrdR.ne', inv_div, div_le_div_iff₀ hQR hsumR]
      have h' : ((a * (cn * rd + rn * cd) : ℕ) : ℝ) ≤ ((Q * (cd * rd) : ℕ) : ℝ) := by
        exact_mod_cast hlo
      push_cast at h'; nlinarith [h']
    exact le_trans hstep (inv_anti₀ hx0 hShi)
  have h2 : x⁻¹ ≤ (b : ℝ) / Q := by
    have hstep : ((cn : ℝ) / cd - (rn : ℝ) / rd)⁻¹ ≤ (b : ℝ) / Q := by
      rw [div_sub_div _ _ hcdR.ne' hrdR.ne', inv_div, div_le_div_iff₀ hdiffR hQR]
      have h' : ((Q * (cd * rd) : ℕ) : ℝ) ≤ ((b * (cn * rd - rn * cd) : ℕ) : ℝ) := by
        exact_mod_cast hhi
      push_cast [hsub] at h'; nlinarith [h']
    exact le_trans (inv_anti₀ hloQ hSlo) hstep
  exact Real.IsNear.of_endpoints hQ h1 h2
end Enclosure
end
end CertificatePort145


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort146
section
namespace Enclosure












end Enclosure
end
end CertificatePort146


section CertificatePort147
section
namespace Enclosure
theorem Real.IsNear.of_eq {x y : ℝ} {n : Bool} {cn cd rn rd : ℕ}
    (he : x = y) (h : Real.IsNear y n cn cd rn rd) : Real.IsNear x n cn cd rn rd := by
  rw [he]; exact h








end Enclosure
end
end CertificatePort147


section CertificatePort148
section
end
end CertificatePort148


section CertificatePort149
section
namespace BSN
open Enclosure
open _root_.Real
def argRoundOk (u v u' v' Dp D : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) v)
    (Nat.add (Nat.sub (nat_lit 1) v')
    (Nat.add (Nat.sub (nat_lit 1) Dp)
    (Nat.add (Nat.sub (nat_lit 1) D)
    (Nat.add (Nat.sub (u'.mul v) (u.mul v'))
             (Nat.sub (Nat.add (Nat.mul (D.mul Dp) (Nat.sub (u.mul v') (u'.mul v)))
                               (Nat.mul D (v.mul v')))
                      (Nat.mul Dp (v.mul v'))))))))
    (nat_lit 0)
private theorem argRoundOk_parts {u v u' v' Dp D : ℕ} (hs : argRoundOk u v u' v' Dp D = true) :
    1 ≤ v ∧ 1 ≤ v' ∧ 1 ≤ Dp ∧ 1 ≤ D ∧ u' * v ≤ u * v' ∧
      D * Dp * (u * v' - u' * v) + D * (v * v') ≤ Dp * (v * v') := by
  simp only [argRoundOk, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, z6⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.le_of_sub_eq_zero z1, Nat.le_of_sub_eq_zero z2, Nat.le_of_sub_eq_zero z3,
    Nat.le_of_sub_eq_zero z4, Nat.le_of_sub_eq_zero z5, Nat.le_of_sub_eq_zero z6⟩
private theorem arg_round_bound {u v u' v' Dp D : ℕ}
    (hv : 1 ≤ v) (hv' : 1 ≤ v') (hDp : 1 ≤ Dp) (hD : 1 ≤ D)
    (hle : u' * v ≤ u * v')
    (hmain : D * Dp * (u * v' - u' * v) + D * (v * v') ≤ Dp * (v * v')) :
    |(u : ℝ) / v - (u' : ℝ) / v'| + 1 / Dp ≤ 1 / D := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hv'R : (0 : ℝ) < v' := by exact_mod_cast hv'
  have hDpR : (0 : ℝ) < Dp := by exact_mod_cast hDp
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hleR : ((u' : ℝ) * v) ≤ (u : ℝ) * v' := by exact_mod_cast hle
  have hnn : (0 : ℝ) ≤ (u : ℝ) * v' - (u' : ℝ) * v := by linarith
  have hsub : ((u * v' - u' * v : ℕ) : ℝ) = (u : ℝ) * v' - (u' : ℝ) * v := by
    have hle' : (u' * v : ℕ) ≤ (u * v' : ℕ) := hle
    push_cast [Nat.cast_sub hle']
    ring
  have hrw : (u : ℝ) / v - (u' : ℝ) / v' = ((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') := by
    field_simp
  have habs : |(u : ℝ) / v - (u' : ℝ) / v'| = ((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') := by
    rw [hrw]
    exact abs_of_nonneg (div_nonneg hnn (by positivity))
  have hmainR : (D : ℝ) * Dp * ((u : ℝ) * v' - (u' : ℝ) * v) + D * (v * v') ≤ Dp * (v * v') := by
    have hc : ((D * Dp * (u * v' - u' * v) + D * (v * v') : ℕ) : ℝ)
        ≤ ((Dp * (v * v') : ℕ) : ℝ) := by
      exact_mod_cast hmain
    push_cast [hsub] at hc
    linarith
  rw [← sub_nonneg, habs]
  have key : (1 : ℝ) / D - (((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') + 1 / Dp)
      = ((Dp : ℝ) * (v * v') - ((D : ℝ) * Dp * ((u : ℝ) * v' - (u' : ℝ) * v) + D * (v * v')))
        / ((D : ℝ) * Dp * (v * v')) := by
    field_simp
  rw [key]
  exact div_nonneg (by linarith) (by positivity)
theorem cos_arg_round {n : Bool} {cn cd : ℕ} (u v u' v' Dp D : ℕ)
    (h : Real.IsNear (Real.cos ((u' : ℝ) / v')) n cn cd 1 Dp)
    (hs : argRoundOk u v u' v' Dp D = true) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) n cn cd 1 D := by
  obtain ⟨hv, hv', hDp, hD, hle, hmain⟩ := argRoundOk_parts hs
  have hb := arg_round_bound hv hv' hDp hD hle hmain
  have hlip : |Real.cos ((u : ℝ) / v) - Real.cos ((u' : ℝ) / v')| ≤ |(u : ℝ) / v - (u' : ℝ) / v'| :=
    Real.abs_cos_sub_cos_le _ _
  have h' : |Real.cos ((u' : ℝ) / v') - sfrac n cn cd| ≤ (1 : ℝ) / Dp := by
    have hh := h
    simp only [Real.IsNear] at hh
    push_cast at hh
    exact hh
  have htri := abs_sub_le (Real.cos ((u : ℝ) / v)) (Real.cos ((u' : ℝ) / v')) (sfrac n cn cd)
  have hres : |Real.cos ((u : ℝ) / v) - sfrac n cn cd| ≤ ((1 : ℕ) : ℝ) / ((D : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hres
theorem sin_arg_round {n : Bool} {cn cd : ℕ} (u v u' v' Dp D : ℕ)
    (h : Real.IsNear (Real.sin ((u' : ℝ) / v')) n cn cd 1 Dp)
    (hs : argRoundOk u v u' v' Dp D = true) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) n cn cd 1 D := by
  obtain ⟨hv, hv', hDp, hD, hle, hmain⟩ := argRoundOk_parts hs
  have hb := arg_round_bound hv hv' hDp hD hle hmain
  have hlip : |Real.sin ((u : ℝ) / v) - Real.sin ((u' : ℝ) / v')| ≤ |(u : ℝ) / v - (u' : ℝ) / v'| :=
    Real.abs_sin_sub_sin_le _ _
  have h' : |Real.sin ((u' : ℝ) / v') - sfrac n cn cd| ≤ (1 : ℝ) / Dp := by
    have hh := h
    simp only [Real.IsNear] at hh
    push_cast at hh
    exact hh
  have htri := abs_sub_le (Real.sin ((u : ℝ) / v)) (Real.sin ((u' : ℝ) / v')) (sfrac n cn cd)
  have hres : |Real.sin ((u : ℝ) / v) - sfrac n cn cd| ≤ ((1 : ℕ) : ℝ) / ((D : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hres
theorem sin_quad0 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ)) * (π / 2)) = Real.sin r := by
  have e : r + (4 * (q : ℝ)) * (π / 2) = r + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi]
theorem sin_quad1 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 1) * (π / 2)) = Real.cos r := by
  have e : r + (4 * (q : ℝ) + 1) * (π / 2) = (r + π / 2) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi_div_two]
theorem sin_quad2 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 2) * (π / 2)) = -Real.sin r := by
  have e : r + (4 * (q : ℝ) + 2) * (π / 2) = (r + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi]
theorem sin_quad3 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 3) * (π / 2)) = -Real.cos r := by
  have e : r + (4 * (q : ℝ) + 3) * (π / 2) = ((r + π / 2) + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi, sin_add_pi_div_two]






theorem reduce_core_val (F r rc q B inner Dinv : ℝ) (ε : ℝ) (g : ℝ → ℝ)
    (hε : |ε| = 1)
    (hquad : F = ε * g r)
    (hlip : |g r - g rc| ≤ |r - rc|)
    (hB : |r - rc| ≤ B)
    (hinner : |g rc - q| ≤ inner)
    (htot : B + inner ≤ Dinv) :
    |F - ε * q| ≤ Dinv := by
  have h1 : |F - ε * q| ≤ |g r - g rc| + |g rc - q| := by
    rw [hquad]
    calc |ε * g r - ε * q| = |ε| * |g r - q| := by rw [← mul_sub, abs_mul]
      _ = |g r - q| := by rw [hε, one_mul]
      _ ≤ |g r - g rc| + |g rc - q| := abs_sub_le _ _ _
  calc |F - ε * q| ≤ |g r - g rc| + |g rc - q| := h1
    _ ≤ B + inner := add_le_add (hlip.trans hB) hinner
    _ ≤ Dinv := htot
theorem reduce_step_val (F x r rcv Pr val : ℝ) (k E Dp D : ℕ) (ε : ℝ) (g : ℝ → ℝ)
    (hε : |ε| = 1)
    (hquad : F = ε * g r)
    (hr : r = x - (k : ℝ) * (π / 2))
    (hlip : |g r - g rcv| ≤ |r - rcv|)
    (hrc : rcv = x - (k : ℝ) * (Pr / 2))
    (hpi : |Real.pi - Pr| ≤ 1 / (E : ℝ))
    (hinner : |g rcv - val| ≤ 1 / (Dp : ℝ))
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((k.mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble ((Nat.mul 2 E).mul Dp)) :
    |F - ε * val| ≤ 1 / (D : ℝ) := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at htot
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  have hDpr : (0 : ℝ) < Dp := pos_real_of_ble hDp
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hB : |r - rcv| ≤ (k : ℝ) / (2 * E) := by
    rw [hr, hrc]
    have e : (x - (k : ℝ) * (π / 2)) - (x - (k : ℝ) * (Pr / 2)) = (k : ℝ) * (Pr / 2 - π / 2) := by
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    have hhalf : |Pr / 2 - π / 2| ≤ 1 / (2 * E) := by
      have e2 : Pr / 2 - π / 2 = -(Real.pi - Pr) / 2 := by ring
      rw [e2, abs_div, abs_neg, abs_two]
      calc |Real.pi - Pr| / 2 ≤ (1 / (E : ℝ)) / 2 := by gcongr
        _ = 1 / (2 * E) := by ring
    calc (k : ℝ) * |Pr / 2 - π / 2| ≤ (k : ℝ) * (1 / (2 * E)) := by gcongr
      _ = (k : ℝ) / (2 * E) := by ring
  have htotR : (k : ℝ) / (2 * E) + 1 / (Dp : ℝ) ≤ 1 / (D : ℝ) := by
    have hc : ((k * D * Dp + 2 * E * D : ℕ) : ℝ) ≤ ((2 * E * Dp : ℕ) : ℝ) := by exact_mod_cast htot
    push_cast at hc
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hc, hEr, hDpr, hDr]
  exact reduce_core_val F r rcv val ((k : ℝ) / (2 * E)) (1 / Dp) (1 / D) ε g hε hquad
    hlip hB hinner htotR
theorem reduce_quad_val (F x rcv : ℝ) (g : ℝ → ℝ) (ε : ℝ) (Pc PQ : ℕ) (ineg oneg : Bool)
    (icn Qd k E Dp D : ℕ)
    (hε : |ε| = 1)
    (hquad : F = ε * g (x - (k : ℝ) * (π / 2)))
    (hlip : ∀ a b, |g a - g b| ≤ |a - b|)
    (hsign : sfrac oneg icn Qd = ε * sfrac ineg icn Qd)
    (hrc : rcv = x - (k : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (g rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((k.mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear F oneg icn Qd 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hpi
  rw [← sfrac_false_div Pc PQ] at hpi
  rw [Real.IsNear, Nat.cast_one] at hinner
  rw [Real.IsNear, Nat.cast_one, hsign]
  exact reduce_step_val F x (x - (k : ℝ) * (π / 2)) rcv (sfrac false Pc PQ)
    (sfrac ineg icn Qd) k E Dp D ε g hε hquad rfl (hlip _ _) hrc hpi hinner hE hDp hD htot
theorem cos_quad0 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ)) * (π / 2)) = Real.cos r := by
  have e : r + (4 * (q : ℝ)) * (π / 2) = r + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi]
theorem cos_quad1 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 1) * (π / 2)) = -Real.sin r := by
  have e : r + (4 * (q : ℝ) + 1) * (π / 2) = (r + π / 2) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi_div_two]
theorem cos_quad2 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 2) * (π / 2)) = -Real.cos r := by
  have e : r + (4 * (q : ℝ) + 2) * (π / 2) = (r + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi]
theorem cos_quad3 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 3) * (π / 2)) = Real.sin r := by
  have e : r + (4 * (q : ℝ) + 3) * (π / 2) = ((r + π / 2) + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi, cos_add_pi_div_two, neg_neg]
theorem sin_reduce0 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : ((((Nat.mul 4 qq).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.sin 1 Pc PQ ineg ineg icn Qd (4 * qq) E Dp D abs_one
    (by rw [one_mul, ← sin_quad0 (x - ((4 * qq : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem sin_reduce1 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).succ).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.cos 1 Pc PQ ineg ineg icn Qd (4 * qq + 1) E Dp D abs_one
    (by rw [one_mul, ← sin_quad1 (x - ((4 * qq + 1 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem sin_reduce2 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 2).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.sin (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 2) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← sin_quad2 (x - ((4 * qq + 2 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem sin_reduce3 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 3).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.cos (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 3) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← sin_quad3 (x - ((4 * qq + 3 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem cos_reduce0 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : ((((Nat.mul 4 qq).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.cos 1 Pc PQ ineg ineg icn Qd (4 * qq) E Dp D abs_one
    (by rw [one_mul, ← cos_quad0 (x - ((4 * qq : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem cos_reduce1 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).succ).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.sin (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 1) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← cos_quad1 (x - ((4 * qq + 1 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 2; push_cast; ring)
    Real.abs_sin_sub_sin_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem cos_reduce2 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 2).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.cos (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 2) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← cos_quad2 (x - ((4 * qq + 2 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 2; push_cast; ring)
    Real.abs_cos_sub_cos_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem cos_reduce3 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 3).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.sin 1 Pc PQ ineg ineg icn Qd (4 * qq + 3) E Dp D
    abs_one
    (by rw [one_mul, ← cos_quad3 (x - ((4 * qq + 3 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem sin_reduce_arg_pos_rat (a b Pc PQ k u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add (k.mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ)) - (k : ℝ) * (sfrac false Pc PQ / 2) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hlink hv
  subst hv
  rw [sfrac_false_div]
  have hQr : (0 : ℝ) < PQ := pos_real_of_ble hQ
  have hbr : (0 : ℝ) < b := pos_real_of_ble hb
  have hlinkR : (2 * a * PQ : ℝ) = (u + k * (b * Pc) : ℝ) := by exact_mod_cast hlink
  push_cast
  field_simp
  ring_nf
  linarith [hlinkR]
theorem sin_reduce_arg_pos_rat_q0 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.mul 4 qq).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ)) - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq) u v hlink hv hQ hb
theorem sin_reduce_arg_pos_rat_q1 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 1).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 1) u v hlink hv hQ hb
theorem sin_reduce_arg_pos_rat_q2 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 2).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 2) u v hlink hv hQ hb
theorem sin_reduce_arg_pos_rat_q3 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 3).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 3) u v hlink hv hQ hb
end BSN
end
end CertificatePort149


section CertificatePort150
section
namespace Enclosure
def Complex.IsNear (z : ℂ)
    (reNeg : Bool) (reCn reCd reRn reRd : ℕ)
    (imNeg : Bool) (imCn imCd imRn imRd : ℕ) : Prop :=
  Real.IsNear z.re reNeg reCn reCd reRn reRd ∧
  Real.IsNear z.im imNeg imCn imCd imRn imRd




theorem Complex.IsNear.mk {re im : ℝ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear re reNeg reCn reCd reRn reRd)
    (him : Real.IsNear im imNeg imCn imCd imRn imRd) :
    Complex.IsNear ⟨re, im⟩ reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := ⟨hre, him⟩


theorem Complex.IsNear.add {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re + w.re) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.im + w.im) imN imCn imCd imRn imRd) :
    Complex.IsNear (z + w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.add_re]; exact hre
  · rw [Complex.add_im]; exact him




def numPosC (neg : Bool) (cn : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) cn 0 neg
def numNegC (neg : Bool) (cn : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) 0 cn neg
theorem numPosC_eq (neg : Bool) (cn : ℕ) : numPosC neg cn = numPos neg cn := by
  cases neg <;> rfl
theorem numNegC_eq (neg : Bool) (cn : ℕ) : numNegC neg cn = numNeg neg cn := by
  cases neg <;> rfl
theorem Complex.IsNear.addLitP {z w : ℂ}
    {nxr : Bool} {cnxr cdxr rnxr rdxr : ℕ} {nxi : Bool} {cnxi cdxi rnxi rdxi : ℕ}
    {nyr : Bool} {cnyr cdyr rnyr rdyr : ℕ} {nyi : Bool} {cnyi cdyi rnyi rdyi : ℕ}
    {nRr : Bool} {cnRr cnRr' cdRr' rnRr' rdRr' : ℕ}
    {nRi : Bool} {cnRi cnRi' cdRi' rnRi' rdRi' : ℕ}
    (h1 : Complex.IsNear z nxr cnxr cdxr rnxr rdxr nxi cnxi cdxi rnxi rdxi)
    (h2 : Complex.IsNear w nyr cnyr cdyr rnyr rdyr nyi cnyi cdyi rnyi rdyi)
    (hcdxr : Nat.ble (nat_lit 1) cdxr) (hcdyr : Nat.ble (nat_lit 1) cdyr)
    (hrdxr : Nat.ble (nat_lit 1) rdxr) (hrdyr : Nat.ble (nat_lit 1) rdyr)
    (hnumr : Nat.beq
      (((numPosC nRr cnRr).add ((numNegC nxr cnxr).mul cdyr)).add
        ((numNegC nyr cnyr).mul cdxr))
      (((numNegC nRr cnRr).add ((numPosC nxr cnxr).mul cdyr)).add
        ((numPosC nyr cnyr).mul cdxr)))
    (hcdRr' : Nat.ble (nat_lit 1) cdRr') (hrdRr' : Nat.ble (nat_lit 1) rdRr')
    (hcr : Nat.beq (cnRr.mul cdRr') (cnRr'.mul (cdxr.mul cdyr)))
    (hrr : Nat.ble (((rnxr.mul rdyr).add (rnyr.mul rdxr)).mul rdRr')
      (rnRr'.mul (rdxr.mul rdyr)))
    (hcdxi : Nat.ble (nat_lit 1) cdxi) (hcdyi : Nat.ble (nat_lit 1) cdyi)
    (hrdxi : Nat.ble (nat_lit 1) rdxi) (hrdyi : Nat.ble (nat_lit 1) rdyi)
    (hnumi : Nat.beq
      (((numPosC nRi cnRi).add ((numNegC nxi cnxi).mul cdyi)).add
        ((numNegC nyi cnyi).mul cdxi))
      (((numNegC nRi cnRi).add ((numPosC nxi cnxi).mul cdyi)).add
        ((numPosC nyi cnyi).mul cdxi)))
    (hcdRi' : Nat.ble (nat_lit 1) cdRi') (hrdRi' : Nat.ble (nat_lit 1) rdRi')
    (hci : Nat.beq (cnRi.mul cdRi') (cnRi'.mul (cdxi.mul cdyi)))
    (hri : Nat.ble (((rnxi.mul rdyi).add (rnyi.mul rdxi)).mul rdRi')
      (rnRi'.mul (rdxi.mul rdyi))) :
    Complex.IsNear (z + w) nRr cnRr' cdRr' rnRr' rdRr' nRi cnRi' cdRi' rnRi' rdRi' := by
  simp only [numPosC_eq, numNegC_eq] at hnumr hnumi
  exact Complex.IsNear.add
    (Real.IsNear.addLit h1.1 h2.1 hcdxr hcdyr hrdxr hrdyr hnumr hcdRr' hrdRr' hcr hrr)
    (Real.IsNear.addLit h1.2 h2.2 hcdxi hcdyi hrdxi hrdyi hnumi hcdRi' hrdRi' hci hri)










theorem Complex.IsNear.of_eq {z w : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (he : z = w) (h : Complex.IsNear w reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := by
  rw [he]; exact h












end Enclosure
end
end CertificatePort150


section CertificatePort151
section
open MeasureTheory Real Filter Topology
open scoped Nat


























end
end CertificatePort151


section CertificatePort152
section
open scoped Nat
namespace Enclosure
theorem natCast_cpow_eq (n : ℕ) (hn : 0 < n) (σ t : ℝ) :
    ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      ⟨Real.exp (σ * Real.log n) * Real.cos (t * Real.log n),
       Real.exp (σ * Real.log n) * Real.sin (t * Real.log n)⟩ := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
  have hstd : ((Real.log n : ℝ) : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)
            = ((Real.log n * σ : ℝ) : ℂ) + ((Real.log n * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [Complex.cpow_def_of_ne_zero hn0, hlog, hstd]
  apply Complex.ext
  · rw [Complex.exp_re]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      add_zero, mul_one]
    congr 1 <;> congr 1 <;> ring
  · rw [Complex.exp_im]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      add_zero, mul_one]
    congr 1 <;> congr 1 <;> ring




end Enclosure
namespace BSN
open Enclosure
open Complex




















theorem complex_zero_mk : (0 : ℂ)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  apply Complex.ext <;> simp [sfrac]
theorem cpow_neg_s_mk (t : ℝ) (tn td n : ℕ) (ht : t = sfrac false tn td)
    (hn : Nat.ble 1 n = true) :
    (n : ℂ) ^ (-(1 / 2 + Complex.I * (t : ℂ)))
      = ⟨(Real.sqrt (n : ℝ))⁻¹
            * Real.cos (sfrac false tn td * Real.log (sfrac false n (nat_lit 1))),
         (Real.sqrt (n : ℝ))⁻¹
            * -Real.sin (sfrac false tn td * Real.log (sfrac false n (nat_lit 1)))⟩ := by
  have hn' : 0 < n := pos_of_ble hn
  have hnR : (0 : ℝ) < n := pos_real_of_ble hn
  have hexp : -(1 / 2 + Complex.I * (t : ℂ))
      = ((-(1/2) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hexp, natCast_cpow_eq n hn' (-(1/2)) (-t)]
  have hmag : Real.exp (-(1 / 2 * Real.log n)) = (Real.sqrt (n : ℝ))⁻¹ := by
    have h1 : ((1 : ℝ) / (n : ℝ)) = Real.exp (-Real.log n) := by
      rw [one_div, Real.exp_neg, Real.exp_log hnR]
    have h2 : Real.exp (-(1 / 2 * Real.log n)) = Real.sqrt (1 / (n : ℝ)) := by
      rw [h1, ← Real.exp_half]
      congr 1
      ring
    rw [h2, one_div, Real.sqrt_inv]
  have hlogsfrac : Real.log (sfrac false n (nat_lit 1)) = Real.log n := by
    rw [sfrac_false_div]; simp
  subst ht
  apply Complex.ext <;>
    simp only [hlogsfrac, neg_mul, Real.cos_neg, Real.sin_neg, hmag]
theorem head_sum_base (s : ℂ) :
    (∑ n ∈ Finset.Ico (1 : ℕ) 1, (n : ℂ) ^ (-s))
        = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [Finset.Ico_self, Finset.sum_empty]
  exact complex_zero_mk
theorem head_sum_succ (s : ℂ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true)
    (ha : Nat.ble 1 a = true) :
    (∑ n ∈ Finset.Ico 1 b, (n : ℂ) ^ (-s))
      = (∑ n ∈ Finset.Ico 1 a, (n : ℂ) ^ (-s)) + (a : ℂ) ^ (-s) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_Ico_succ_top (Nat.le_of_ble_eq_true ha) _
noncomputable def headSumC (s : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)
theorem head_sum_c_base (s : ℂ) : headSumC s (nat_lit 1)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ :=
  head_sum_base s
theorem head_sum_c_succ (s : ℂ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true)
    (ha : Nat.ble 1 a = true) : headSumC s b = headSumC s a + (a : ℂ) ^ (-s) :=
  head_sum_succ s a b hb ha
theorem head_sum_c_two (s : ℂ) :
    headSumC s (nat_lit 2)
      = ⟨sfrac false (nat_lit 1) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [head_sum_c_succ s (nat_lit 1) (nat_lit 2) (by rfl) (by rfl), head_sum_c_base, Nat.cast_one,
    Complex.one_cpow]
  apply Complex.ext <;> simp [sfrac]






















































































































































































end BSN
end
end CertificatePort152


section CertificatePort153
section
namespace BSN
open Enclosure


theorem log_reduce_eq (N M k : ℕ) (hN : 0 < N) (hM : 0 < M) :
    Real.log ((N : ℝ) / M) = Real.log ((N : ℝ) / (M * 2 ^ k)) + (k : ℝ) * Real.log 2 := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have e : (N : ℝ) / (M * 2 ^ k) = ((N : ℝ) / M) / 2 ^ k := by rw [div_div]
  have key : Real.log ((N : ℝ) / (M * 2 ^ k)) = Real.log ((N : ℝ) / M) - (k : ℝ) * Real.log 2 := by
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_pow]
  rw [key]; ring
theorem log_rat_reduce_isNear (a b k S Dd pr Qr p2 Q2 D E : ℕ) (ha : Nat.ble 1 a)
    (hb : Nat.ble 1 b)
    (hS : S.beq (Nat.mul 2 a)) (hDd : Dd.beq (Nat.mul b (Nat.pow 2 (Nat.succ k))))
    (hr : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) false pr Qr 1 D)
    (h2 : Real.IsNear (Real.log 2) false p2 Q2 1 E)
    (hD : Nat.ble 1 D) (hE : Nat.ble 1 E) (hQr : Nat.ble 1 Qr) (hQ2 : Nat.ble 1 Q2) :
    Real.IsNear (Real.log ((a : ℝ) / b)) false ((pr.mul Q2).add ((k.mul p2).mul Qr)) (Qr.mul Q2)
      (E.add (k.mul D)) (D.mul E) := by
  obtain rfl := Nat.eq_of_beq_eq_true hS
  obtain rfl := Nat.eq_of_beq_eq_true hDd
  simp only [Nat.mul_eq, Nat.add_eq, Nat.pow_eq] at hr ⊢
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hr h2
  have hDR : (0:ℝ) < D := pos_real_of_ble hD
  have hER : (0:ℝ) < E := pos_real_of_ble hE
  have hQrR : (0:ℝ) < Qr := pos_real_of_ble hQr
  have hQ2R : (0:ℝ) < Q2 := pos_real_of_ble hQ2
  have harg : ((↑(2 * a) : ℝ) / ((b * 2 ^ (k + 1) : ℕ) : ℝ)) = (↑a : ℝ) / ((b : ℝ) * 2 ^ k) := by
    push_cast; ring
  rw [harg] at hr
  have hlogn : Real.log ((↑a : ℝ) / b)
      = Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) + ↑k * Real.log 2 :=
    log_reduce_eq a b k (pos_of_ble ha) (pos_of_ble hb)
  have hcentre : ((pr * Q2 + k * p2 * Qr : ℕ) : ℝ) / ((Qr * Q2 : ℕ) : ℝ)
              = (pr : ℝ) / Qr + ↑k * ((p2 : ℝ) / Q2) := by
    push_cast; field_simp [hQrR.ne', hQ2R.ne']
  have hrad : ((E + k * D : ℕ) : ℝ) / ((D * E : ℕ) : ℝ) = 1 / ↑D + ↑k * (1 / ↑E) := by
    push_cast; field_simp [hDR.ne', hER.ne']
  rw [Real.IsNear, sfrac_false_div, hlogn, hcentre, hrad]
  calc |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) + ↑k * Real.log 2
          - ((pr : ℝ) / Qr + ↑k * ((p2 : ℝ) / Q2))|
      = |(Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr)
          + ↑k * (Real.log 2 - (p2 : ℝ) / Q2)| := by ring_nf
    _ ≤ |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr|
          + |↑k * (Real.log 2 - (p2 : ℝ) / Q2)| := abs_add_le _ _
    _ = |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr|
          + ↑k * |Real.log 2 - (p2 : ℝ) / Q2| := by rw [abs_mul, Nat.abs_cast]
    _ ≤ 1 / ↑D + ↑k * (1 / ↑E) := by gcongr


theorem logfrac_isNear (S Dd g a b p Q D : ℕ) (hg : Nat.ble 1 g)
    (hs : Nat.beq (S.mul g) (Nat.mul 2 a))
    (hd : Nat.beq (Dd.mul g) (Nat.mul 2 b))
    (h : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) false p Q 1 D) :
    Real.IsNear (Real.log ((a : ℝ) / b)) false p Q 1 D := by
  have hs' : S * g = 2 * a := Nat.eq_of_beq_eq_true hs
  have hd' : Dd * g = 2 * b := Nat.eq_of_beq_eq_true hd
  have hgR : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_ble hg).ne'
  have h1 : (S : ℝ) * g = 2 * a := by exact_mod_cast hs'
  have h2 : (Dd : ℝ) * g = 2 * b := by exact_mod_cast hd'
  have e : ((S : ℝ) / (Dd : ℝ)) = (a : ℝ) / b := by
    calc (S : ℝ) / (Dd : ℝ)
        = (S : ℝ) * g / ((Dd : ℝ) * g) := (mul_div_mul_right _ _ hgR).symm
      _ = 2 * (a : ℝ) / (2 * (b : ℝ)) := by rw [h1, h2]
      _ = (a : ℝ) / b := mul_div_mul_left _ _ two_ne_zero
  rwa [e] at h
end BSN
end
end CertificatePort153


section CertificatePort156
section
namespace BSN




open Finset in
theorem alt_series_tail_bound (x : ℝ) (E : ℕ) (f : ℕ → ℝ) (N : ℕ) (hx : 0 ≤ x)
    (hsummable : Summable f) (hxE : x < E + 1)
    (hnorm : ∀ j, ‖f (j + N)‖ = x ^ (E + 2 * j) / (E + 2 * j).factorial) :
    |∑' j, f (j + N)| ≤ x ^ E / E.factorial * (1 - (x / (E + 1)) ^ 2)⁻¹ := by
  have hb : x / (E + 1) < 1 := by rw [div_lt_one (by positivity)]; exact hxE
  have hr : (0:ℝ) ≤ (x / (E + 1)) ^ 2 := by positivity
  have hr1 : (x / (E + 1)) ^ 2 < 1 := pow_lt_one₀ (by positivity) hb (by norm_num)
  have htsumnorm : Summable (fun j => ‖f (j + N)‖) :=
    ((summable_nat_add_iff N).2 hsummable).norm
  have hgeo : Summable (fun j => x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j) :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have hterm : ∀ j, ‖f (j + N)‖ ≤ x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j := by
    intro j
    rw [hnorm]
    have hfac : (E.factorial : ℝ) * (E + 1) ^ (2 * j) ≤ ((E + 2 * j).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_pow_le_factorial (m := E) (n := 2 * j)
    have hnum : (0:ℝ) ≤ x ^ E * x ^ (2 * j) := by positivity
    calc x ^ (E + 2 * j) / ((E + 2 * j).factorial : ℝ)
        = (x ^ E * x ^ (2 * j)) / ((E + 2 * j).factorial : ℝ) := by rw [pow_add]
      _ ≤ (x ^ E * x ^ (2 * j)) / (E.factorial * (E + 1) ^ (2 * j)) :=
          div_le_div_of_nonneg_left hnum (by positivity) hfac
      _ = x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j := by rw [← pow_mul, div_pow]; ring
  calc |∑' j, f (j + N)|
      = ‖∑' j, f (j + N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, ‖f (j + N)‖ := norm_tsum_le_tsum_norm htsumnorm
    _ ≤ ∑' j, x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j := htsumnorm.tsum_le_tsum hterm hgeo
    _ = x ^ E / E.factorial * ∑' j, ((x / (E + 1)) ^ 2) ^ j := tsum_mul_left
    _ = x ^ E / E.factorial * (1 - (x / (E + 1)) ^ 2)⁻¹ := by rw [tsum_geometric_of_lt_one hr hr1]
open Finset in
theorem sin_sub_sum_le (x : ℝ) (N : ℕ) (hx : 0 ≤ x) (hxN : x < 2 * N + 2) :
    |Real.sin x - ∑ k ∈ range N, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1).factorial| ≤
      x ^ (2 * N + 1) / (2 * N + 1).factorial * (1 - (x / (2 * N + 2)) ^ 2)⁻¹ := by
  set f : ℕ → ℝ := fun n => (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1).factorial with hf
  have hsummable : Summable f := (Real.hasSum_sin x).summable
  have hsin : Real.sin x = ∑' n, f n := Real.sin_eq_tsum x
  have htail : Real.sin x - ∑ k ∈ range N, f k = ∑' j, f (j + N) := by
    rw [hsin, ← hsummable.sum_add_tsum_nat_add N]; ring
  rw [htail]
  have hnorm : ∀ j, ‖f (j + N)‖ = x ^ (2 * N + 1 + 2 * j) / (2 * N + 1 + 2 * j).factorial := by
    intro j
    have he : 2 * (j + N) + 1 = 2 * N + 1 + 2 * j := by ring
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hx, Nat.abs_cast, he]
  refine (alt_series_tail_bound x (2 * N + 1) f N hx hsummable (by push_cast; linarith)
    hnorm).trans_eq ?_
  push_cast; ring
open Finset in
theorem cos_sub_sum_le (x : ℝ) (N : ℕ) (hx : 0 ≤ x) (hxN : x < 2 * N + 1) :
    |Real.cos x - ∑ k ∈ range N, (-1) ^ k * x ^ (2 * k) / (2 * k).factorial| ≤
      x ^ (2 * N) / (2 * N).factorial * (1 - (x / (2 * N + 1)) ^ 2)⁻¹ := by
  set f : ℕ → ℝ := fun n => (-1) ^ n * x ^ (2 * n) / (2 * n).factorial with hf
  have hsummable : Summable f := (Real.hasSum_cos x).summable
  have hcos : Real.cos x = ∑' n, f n := Real.cos_eq_tsum x
  have htail : Real.cos x - ∑ k ∈ range N, f k = ∑' j, f (j + N) := by
    rw [hcos, ← hsummable.sum_add_tsum_nat_add N]; ring
  rw [htail]
  have hnorm : ∀ j, ‖f (j + N)‖ = x ^ (2 * N + 2 * j) / (2 * N + 2 * j).factorial := by
    intro j
    have he : 2 * (j + N) = 2 * N + 2 * j := by ring
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hx, Nat.abs_cast, he]
  refine (alt_series_tail_bound x (2 * N) f N hx hsummable (by push_cast; linarith)
    hnorm).trans_eq ?_
  push_cast; ring


theorem geo_factor_le (x D : ℝ) (hD : 0 < D) (hx : 2 * x ^ 2 ≤ D ^ 2) :
    (1 - (x / D) ^ 2)⁻¹ ≤ 2 := by
  have h2 : (x / D) ^ 2 ≤ 1 / 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  rw [← one_div]
  calc 1 / (1 - (x / D) ^ 2) ≤ 1 / (1 / 2) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
    _ = 2 := by norm_num
theorem factorial_add_four (m : ℕ) :
    (m + 4).factorial = m.factorial * ((m + 1) * (m + 2) * (m + 3) * (m + 4)) := by
  have e : m + 4 = m + 1 + 1 + 1 + 1 := rfl
  rw [e, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  ring
open Finset in
theorem sum_range_two_mul {α} [AddCommMonoid α] (f : ℕ → α) (M : ℕ) :
    ∑ i ∈ range (2 * M), f i = ∑ j ∈ range M, (f (2 * j) + f (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    abel
theorem sub_grid_round (F Ne De No Do : ℝ) (m : ℤ) (Q D : ℕ)
    (hFV : |F - (Ne / De - No / Do)| ≤ 1 / (2 * D))
    (hr1 : (m : ℝ) * (De * Do) ≤ (Ne * Do - No * De) * Q)
    (hr2 : (Ne * Do - No * De) * Q < ((m : ℝ) + 1) * (De * Do))
    (hDe : 0 < De) (hDo : 0 < Do) (hDr : 0 < (D : ℝ)) (hQr : 0 < (Q : ℝ))
    (hQ : 2 * D ≤ Q) :
    |F - (m : ℝ) / Q| ≤ 1 / D := by
  have hd : (0 : ℝ) < De * Do := mul_pos hDe hDo
  have hV : Ne / De - No / Do = (Ne * Do - No * De) / (De * Do) := by field_simp
  have e1 : (m : ℝ) / Q ≤ (Ne * Do - No * De) / (De * Do) := by
    rw [div_le_div_iff₀ hQr hd]; exact hr1
  have e2 : (Ne * Do - No * De) / (De * Do) < (m : ℝ) / Q + 1 / Q := by
    rw [← add_div, div_lt_div_iff₀ hd hQr]; exact hr2
  have hround' : |(Ne / De - No / Do) - (m : ℝ) / Q| ≤ 1 / (2 * D) := by
    rw [hV, abs_of_nonneg (sub_nonneg.mpr e1)]
    calc (Ne * Do - No * De) / (De * Do) - (m : ℝ) / Q
        ≤ 1 / Q := by linarith [e2]
      _ ≤ 1 / (2 * D) := by
          rw [div_le_div_iff₀ hQr (mul_pos two_pos hDr), one_mul, one_mul]; exact_mod_cast hQ
  calc |F - (m : ℝ) / Q|
      ≤ |F - (Ne / De - No / Do)| + |(Ne / De - No / Do) - (m : ℝ) / Q| := abs_sub_le _ _ _
    _ ≤ 1 / (2 * D) + 1 / (2 * D) := add_le_add hFV hround'
    _ = 1 / D := by rw [← add_div, one_add_one_eq_two, ← div_div, div_self two_ne_zero]
end BSN
end
end CertificatePort156


section CertificatePort157
section
namespace BSN
open Enclosure
open Finset
















end BSN
end
end CertificatePort157


section CertificatePort159
section
namespace BSN
open Enclosure
open Finset
theorem prod_even_denom (j : ℕ) :
    ∏ k ∈ range j, ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5))
        = (4 * j + 1).factorial := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : 4 * (n + 1) + 1 = (4 * n + 1) + 4 := by ring
    rw [prod_range_succ, ih, e, factorial_add_four]
theorem prod_odd_denom (j : ℕ) :
    (∏ k ∈ range j, ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7))) * 6 =
      (4 * j + 3).factorial := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have e : 4 * (n + 1) + 3 = (4 * n + 3) + 4 := by ring
    rw [prod_range_succ, e, factorial_add_four, ← ih]
    ring
theorem sinEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((sinEvenP u k : ℚ) / (sinEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [sinEvenP, sinEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial := by
    have keyN : ∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5)))
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, prod_even_denom]
    exact_mod_cast keyN
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem sinEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (sinEvenP u) (sinEvenQ v) 0 (M - 1)) :
    ((u : ℚ) * (Q + T) / (v * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 1) / ((v : ℚ) ^ (4 * j + 1) * (4 * j + 1).factorial) := by
  have hqne : ∀ i, sinEvenQ v i ≠ 0 := by
    intro i; simp only [sinEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => sinEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 1) / ((v : ℚ) ^ (4 * (i + 1) + 1) * (4 * (i + 1) + 1).factorial)
        = (u : ℚ) / v *
          ((u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial)) := by
    intro i _
    rw [pow_succ' (u : ℚ), pow_succ' (v : ℚ)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
  field_simp
  ring
theorem sinOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((sinOddP u k : ℚ) / (sinOddQ v k))
      = 6 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [sinOddP, sinOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial / 6 := by
    have keyN : (∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)))) * 6
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_odd_denom]
    have keyQ : (∏ k ∈ Finset.range (i + 1),
        ((v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)) : ℕ) : ℚ)) * 6
        = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (6 : ℚ) ≠ 0)]
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 3).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem sinOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (sinOddP u) (sinOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 3 * (Q + T) / (6 * v ^ 3 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 3) / ((v : ℚ) ^ (4 * j + 3) * (4 * j + 3).factorial) := by
  have hqne : ∀ i, sinOddQ v i ≠ 0 := by
    intro i; simp only [sinOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := sinOddP u) (q := sinOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := sinOddP u) (q := sinOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => sinOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 3) / ((v : ℚ) ^ (4 * (i + 1) + 3) * (4 * (i + 1) + 3).factorial)
        = (u : ℚ) ^ 3 / (6 * v ^ 3) *
          (6 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial)) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 3, pow_add (v : ℚ) (4 * (i + 1)) 3]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_succ, Nat.factorial_zero]
  push_cast
  field_simp
  ring
theorem sin_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : (((numPos neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  have hMpos0 : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hbridge : v * (Qe * sinEvenQ v (M - 1))
      = v ^ (2 * (2 * M) + 1) * (2 * (2 * M) + 1).factorial := by
    have hQeprod : Qe = ∏ k ∈ Finset.range (M - 1), sinEvenQ v k := by
      have h := (binarySplit_PQ (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1)).2
      rw [heven, ← Finset.range_eq_Ico] at h; exact h
    rw [hQeprod, ← Finset.prod_range_succ, show M - 1 + 1 = M from by omega]
    simp only [sinEvenQ, Nat.pow_eq, Nat.mul_eq, Nat.add_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, prod_even_denom,
      show 2 * (2 * M) + 1 = 4 * M + 1 from by ring, pow_succ]
    ring
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQeN : 0 < Qe := pos_of_ble hQe
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := sinEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := sinOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : (u : ℚ) * (Qe + Te) / (v * Qe) - (u : ℚ) ^ 3 * (Qo + To) / (6 * v ^ 3 * Qo)
      = ∑ i ∈ Finset.range (2 * M),
          (-1) ^ i * ((u : ℚ) / v) ^ (2 * i + 1) / (2 * i + 1).factorial := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) + 1 = 4 * j + 1 := by ring
    have e2 : 2 * (2 * j + 1) + 1 = 4 * j + 3 := by ring
    rw [e1, e2, s1, s2, div_pow, div_pow]
    ring
  set m : ℤ := (mp : ℤ) - (mn : ℤ) with hm
  rw [Real.IsNear, Nat.cast_one]
  have hvform : sfrac neg cn Q = (m : ℝ) / Q := by
    rw [sfrac_eq_parts neg cn Q, ← hmp_def, ← hmn_def, hm]
    push_cast
    ring
  rw [hvform]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at hu hu2 htail hQ hr1 hr2
  set De := v * Qe with hDe_def
  set Do := 6 * v ^ 3 * Qo with hDo_def
  set Ne := u * (Qe + Te) with hNe_def
  set No := u ^ 3 * (Qo + To) with hNo_def
  have hDeR : (De : ℝ) = (v : ℝ) * Qe := by rw [hDe_def]; push_cast; ring
  have hDoR : (Do : ℝ) = 6 * (v : ℝ) ^ 3 * Qo := by rw [hDo_def]; push_cast; ring
  have hr1z : m * ((De : ℤ) * Do) ≤ ((Ne : ℤ) * Do - (No : ℤ) * De) * Q := by
    have h : (mp : ℤ) * ((De : ℤ) * Do) + (No : ℤ) * De * Q
        ≤ (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do) := by exact_mod_cast hr1
    have e1 : m * ((De : ℤ) * Do) = (mp : ℤ) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by
      rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hr2z : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q < (m + 1) * ((De : ℤ) * Do) := by
    have h : (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do)
        < (mp + 1) * ((De : ℤ) * Do) + (No : ℤ) * De * Q := by exact_mod_cast hr2
    have e1 : (m + 1) * ((De : ℤ) * Do)
        = (mp + 1) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hDe0 : (0 : ℝ) < De := by rw [hDeR]; positivity
  have hDo0 : (0 : ℝ) < Do := by rw [hDoR]; positivity
  have hvalR : ((Ne : ℝ) / De - (No : ℝ) / Do)
      = ∑ i ∈ Finset.range (2 * M),
          (-1) ^ i * ((u : ℝ) / v) ^ (2 * i + 1) / (2 * i + 1).factorial := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDe_def, hNo_def, hDo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((2 * M : ℕ) : ℝ) + 2 := by
    rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hsin := sin_sub_sum_le ((u : ℝ) / v) (2 * M) hxnn hxlt
  rw [← hvalR] at hsin
  have hsin' : |Real.sin ((u : ℝ) / v) - ((Ne : ℝ) / De - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine hsin.trans ?_
    have hA2 : ((u : ℝ) / v) ^ (2 * (2 * M) + 1) / (2 * (2 * M) + 1).factorial * 2
        ≤ 1 / (2 * D) := by
      rw [div_pow, div_div, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have e : (u : ℝ) ^ (2 * (2 * M) + 1) * 2 * (2 * D)
          = 2 * (u : ℝ) ^ (2 * (2 * M) + 1) * (2 * D) := by ring
      rw [e]
      have htR : 2 * (u : ℝ) ^ (2 * (2 * M) + 1) * (2 * D)
          ≤ (v : ℝ) * (Qe : ℝ) * (sinEvenQ v (M - 1) : ℝ) := by exact_mod_cast htail
      have hbR : (v : ℝ) * (Qe : ℝ) * (sinEvenQ v (M - 1) : ℝ)
          = (v : ℝ) ^ (2 * (2 * M) + 1) * ((2 * (2 * M) + 1).factorial : ℝ) := by
        have hb : v * Qe * sinEvenQ v (M - 1)
            = v ^ (2 * (2 * M) + 1) * (2 * (2 * M) + 1).factorial := by
          rw [Nat.mul_assoc]; exact hbridge
        exact_mod_cast hb
      exact le_of_le_of_eq htR hbR
    refine le_trans ?_ hA2
    gcongr
    exact geo_factor_le _ _ (by positivity) (by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      exact_mod_cast hu2)
  have hr1' : (m : ℝ) * ((De : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * De) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * De) * Q < ((m : ℝ) + 1) * ((De : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.sin ((u : ℝ) / v)) (Ne : ℝ) (De : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hsin' hr1' hr2' hDe0 hDo0 hDr hQr hQ
theorem sin_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : ((cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      (((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q)).blt
      ((((cn.succ)).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) false cn Q 1 D := by
  refine sin_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega




end BSN
end
end CertificatePort159


section CertificatePort161
section
namespace BSN
open Enclosure
open Finset
theorem prod_cosEven_denom (j : ℕ) :
    ∏ k ∈ range j, ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)) = (4 * j).factorial := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : 4 * (n + 1) = (4 * n) + 4 := by ring
    rw [prod_range_succ, ih, e, factorial_add_four]
theorem prod_cosOdd_denom (j : ℕ) :
    (∏ k ∈ range j, ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6))) * 2 =
      (4 * j + 2).factorial := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have e : 4 * (n + 1) + 2 = (4 * n + 2) + 4 := by ring
    rw [prod_range_succ, e, factorial_add_four, ← ih]
    ring
theorem cosEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((cosEvenP u k : ℚ) / (cosEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1)).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [cosEvenP, cosEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1)).factorial := by
    have keyN : ∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)))
        = v ^ (4 * (i + 1)) * (4 * (i + 1)).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
        prod_cosEven_denom]
    exact_mod_cast keyN
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1)).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem cosEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (cosEvenP u) (cosEvenQ v) 0 (M - 1)) :
    (((Q + T : ℕ) : ℚ) / Q)
      = ∑ j ∈ Finset.range M, (u : ℚ) ^ (4 * j) / ((v : ℚ) ^ (4 * j) * (4 * j).factorial) := by
  have hqne : ∀ i, cosEvenQ v i ≠ 0 := by
    intro i; simp only [cosEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => cosEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ', hspec]
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  push_cast
  field_simp
  ring
theorem cosOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((cosOddP u k : ℚ) / (cosOddQ v k))
      = 2 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [cosOddP, cosOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial / 2 := by
    have keyN : (∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)))) * 2
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_cosOdd_denom]
    have keyQ : (∏ k ∈ Finset.range (i + 1),
        ((v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)) : ℕ) : ℚ)) * 2
        = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)]
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem cosOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (cosOddP u) (cosOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 2 * (Q + T) / (2 * v ^ 2 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 2) / ((v : ℚ) ^ (4 * j + 2) * (4 * j + 2).factorial) := by
  have hqne : ∀ i, cosOddQ v i ≠ 0 := by
    intro i; simp only [cosOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := cosOddP u) (q := cosOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := cosOddP u) (q := cosOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => cosOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 2) / ((v : ℚ) ^ (4 * (i + 1) + 2) * (4 * (i + 1) + 2).factorial)
        = (u : ℚ) ^ 2 / (2 * v ^ 2) *
          (2 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial)) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 2, pow_add (v : ℚ) (4 * (i + 1)) 2]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_two]
  push_cast
  field_simp
  ring
theorem cos_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : (((numPos neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)).ble
      ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  have hMpos0 : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hbridge : Qe * cosEvenQ v (M - 1) = v ^ (2 * (2 * M)) * (2 * (2 * M)).factorial := by
    have hQeprod : Qe = ∏ k ∈ Finset.range (M - 1), cosEvenQ v k := by
      have h := (binarySplit_PQ (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1)).2
      rw [heven, ← Finset.range_eq_Ico] at h; exact h
    rw [hQeprod, ← Finset.prod_range_succ, show M - 1 + 1 = M from by omega]
    simp only [cosEvenQ, Nat.pow_eq, Nat.mul_eq, Nat.add_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
      prod_cosEven_denom, show 4 * M = 2 * (2 * M) from by ring]
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := cosEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := cosOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : ((Qe + Te : ℕ) : ℚ) / Qe - (u : ℚ) ^ 2 * (Qo + To) / (2 * v ^ 2 * Qo)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℚ) / v) ^ (2 * i) / (2 * i).factorial := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) = 4 * j := by ring
    have e2 : 2 * (2 * j + 1) = 4 * j + 2 := by ring
    rw [e1, e2, s1, s2, div_pow, div_pow]
    ring
  set m : ℤ := (mp : ℤ) - (mn : ℤ) with hm
  rw [Real.IsNear, Nat.cast_one]
  have hvform : sfrac neg cn Q = (m : ℝ) / Q := by
    rw [sfrac_eq_parts neg cn Q, ← hmp_def, ← hmn_def, hm]
    push_cast
    ring
  rw [hvform]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at hu hu2 htail hQ hr1 hr2
  push_cast at hcombine
  set Do := 2 * v ^ 2 * Qo with hDo_def
  set Ne := Qe + Te with hNe_def
  set No := u ^ 2 * (Qo + To) with hNo_def
  have hDoR : (Do : ℝ) = 2 * (v : ℝ) ^ 2 * Qo := by rw [hDo_def]; push_cast; ring
  have hr1z : m * ((Qe : ℤ) * Do) ≤ ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q := by
    have h : (mp : ℤ) * ((Qe : ℤ) * Do) + (No : ℤ) * Qe * Q
        ≤ (Ne : ℤ) * Do * Q + (mn : ℤ) * ((Qe : ℤ) * Do) := by exact_mod_cast hr1
    have e1 : m * ((Qe : ℤ) * Do) = (mp : ℤ) * ((Qe : ℤ) * Do) - (mn : ℤ) * ((Qe : ℤ) * Do) := by
      rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * Qe * Q := by ring
    rw [e1, e2]; linarith
  have hr2z : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q < (m + 1) * ((Qe : ℤ) * Do) := by
    have h : (Ne : ℤ) * Do * Q + (mn : ℤ) * ((Qe : ℤ) * Do)
        < (mp + 1) * ((Qe : ℤ) * Do) + (No : ℤ) * Qe * Q := by exact_mod_cast hr2
    have e1 : (m + 1) * ((Qe : ℤ) * Do)
        = (mp + 1) * ((Qe : ℤ) * Do) - (mn : ℤ) * ((Qe : ℤ) * Do) := by rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * Qe * Q := by ring
    rw [e1, e2]; linarith
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQe0 : (0 : ℝ) < Qe := pos_real_of_ble hQe
  have hDo0 : (0 : ℝ) < Do := by rw [hDoR]; positivity
  have hvalR : ((Ne : ℝ) / Qe - (No : ℝ) / Do)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℝ) / v) ^ (2 * i) / (2 * i).factorial := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDo_def, hNo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((2 * M : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hcos := cos_sub_sum_le ((u : ℝ) / v) (2 * M) hxnn hxlt
  rw [← hvalR] at hcos
  have hcos' : |Real.cos ((u : ℝ) / v) - ((Ne : ℝ) / Qe - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine hcos.trans ?_
    have hA2 : ((u : ℝ) / v) ^ (2 * (2 * M)) / (2 * (2 * M)).factorial * 2 ≤ 1 / (2 * D) := by
      rw [div_pow, div_div, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have e : (u : ℝ) ^ (2 * (2 * M)) * 2 * (2 * D)
          = 2 * (u : ℝ) ^ (2 * (2 * M)) * (2 * D) := by ring
      rw [e]
      have htR : 2 * (u : ℝ) ^ (2 * (2 * M)) * (2 * D) ≤ (Qe : ℝ) * (cosEvenQ v (M - 1) : ℝ) := by
        exact_mod_cast htail
      have hbR : (Qe : ℝ) * (cosEvenQ v (M - 1) : ℝ)
          = (v : ℝ) ^ (2 * (2 * M)) * ((2 * (2 * M)).factorial : ℝ) := by exact_mod_cast hbridge
      exact le_of_le_of_eq htR hbR
    refine le_trans ?_ hA2
    gcongr
    exact geo_factor_le _ _ (by positivity) (by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      exact_mod_cast hu2)
  have hr1' : (m : ℝ) * ((Qe : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * Qe) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * Qe) * Q < ((m : ℝ) + 1) * ((Qe : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.cos ((u : ℝ) / v)) (Ne : ℝ) (Qe : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hcos' hr1' hr2' hQe0 hDo0 hDr hQr hQ
theorem cos_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : ((cn.mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)).ble
      (((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q)).blt
      (((cn.succ).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) false cn Q 1 D := by
  refine cos_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega




end BSN
end
end CertificatePort161


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort163
section
namespace BSN
open Enclosure
open Finset
private theorem prod_2k3 (i : ℕ) :
    ∏ k ∈ range i, (2 * k + 3) = (∏ k ∈ range i, (2 * k + 1)) * (2 * i + 1) := by
  induction i with
  | zero => simp
  | succ n ih => rw [prod_range_succ, ih, prod_range_succ]; ring
theorem artanh_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ j ∈ Finset.Ico 0 (i + 1), ((artanhP u j : ℚ) / (artanhQ v j))
      = ((u : ℚ) / v) ^ (2 * (i + 1)) / ((2 * (i + 1) + 1 : ℕ) : ℚ) := by
  rw [← Finset.range_eq_Ico]
  simp only [artanhP, artanhQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib]
  have hnum : (∏ k ∈ Finset.range (i + 1), ((u ^ 2 * (2 * k + 1) : ℕ) : ℚ))
      = (u : ℚ) ^ (2 * (i + 1)) * ∏ k ∈ Finset.range (i + 1), ((2 * k + 1 : ℕ) : ℚ) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hden : (∏ k ∈ Finset.range (i + 1), ((v ^ 2 * (2 * k + 3) : ℕ) : ℚ))
      = (v : ℚ) ^ (2 * (i + 1)) *
        ((∏ k ∈ Finset.range (i + 1), ((2 * k + 1 : ℕ) : ℚ)) * (2 * (i + 1) + 1)) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
    congr 1
    exact_mod_cast prod_2k3 (i + 1)
  rw [hnum, hden, div_pow]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hp1 : (∏ k ∈ Finset.range (i + 1), ((2 * k + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp
theorem artanh_value (u v N T Q P : ℕ) (hv : v ≠ 0) (hN : 1 ≤ N)
    (h : (T, Q, P) = binarySplit (artanhP u) (artanhQ v) 0 (N - 1)) :
    ((u : ℚ) * (Q + T) / (v * Q))
      = ∑ i ∈ Finset.range N, ((u : ℚ) / v) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ) := by
  have hqne : ∀ i, artanhQ v i ≠ 0 := by
    intro i; simp only [artanhQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 2 hv) (by omega)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := artanhP u) (q := artanhQ v)
      (m := 0) (n := N - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := artanhP u) (q := artanhQ v)
    (m := 0) (n := N - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => artanh_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : N = N - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (N - 1),
      ((u : ℚ) / v) ^ (2 * (i + 1) + 1) / ((2 * (i + 1) + 1 : ℕ) : ℚ)
        = ((u : ℚ) / v) * (((u : ℚ) / v) ^ (2 * (i + 1)) / ((2 * (i + 1) + 1 : ℕ) : ℚ)) := by
    intro i _
    rw [pow_succ']
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.cast_one, div_one]
  field_simp
  ring
theorem log_dyadic_bound (u v N Nm Qd Qdy D T P p S Dd : ℕ)
    (huv : u.blt v) (hg : (Nat.mul 2 (u.pow 2)).ble (v.pow 2)) (hQd : Nat.ble 1 Qd)
    (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hN : Nat.ble 1 N) (hNm : (Nm.succ).beq N)
    (hS : S.beq (v.add u)) (hDd : Dd.beq (v.sub u))
    (hsplit : binarySplit (artanhP u) (artanhQ v) 0 Nm = (T, Qd, P))
    (htail : ((Nat.mul 4 (u.pow ((Nat.mul 2 N).succ))).mul (Nat.mul 2 D)).ble
      (v.pow ((Nat.mul 2 N).succ)))
    (hr1 : (p.mul (v.mul Qd)).ble ((Nat.mul 2 (u.mul (Qd.add T))).mul Qdy))
    (hr2 : ((Nat.mul 2 (u.mul (Qd.add T))).mul Qdy).blt ((p.succ).mul (v.mul Qd)))
    (hQ : (Nat.mul 2 D).ble Qdy) :
    Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) false p Qdy 1 D := by
  have hNm' : Nm = N - 1 := by
    have h : Nm + 1 = N := Nat.eq_of_beq_eq_true hNm
    omega
  subst hNm'
  obtain rfl : S = v + u := Nat.eq_of_beq_eq_true hS
  obtain rfl : Dd = v - u := Nat.eq_of_beq_eq_true hDd
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one]
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at huv hg hQd hD hv hN htail hr1 hr2 hQ
  have hQdy0 : 0 < Qdy := by omega
  have hQdyr : (0 : ℝ) < Qdy := by exact_mod_cast hQdy0
  have hvne : v ≠ 0 := by omega
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  have hQd0 : (0 : ℝ) < Qd := by exact_mod_cast (by omega : 0 < Qd)
  have hden0 : (0 : ℝ) < (v : ℝ) * Qd := mul_pos hv0 hQd0
  have hsumR : (u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd)
      = ∑ i ∈ Finset.range N, ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
    have hq := artanh_value u v N T Qd P hvne hN hsplit.symm
    have hr := congrArg (fun r : ℚ => (r : ℝ)) hq
    push_cast at hr
    rw [hr]
  have hlog' : |Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ))
        - 2 * ((u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd))| ≤ 1 / (2 * D) := by
    have hx : |(u : ℝ) / v| < 1 := by
      rw [abs_of_nonneg (by positivity), div_lt_one hv0]; exact_mod_cast huv
    have hm := Real.sum_range_sub_log_div_le hx N
    have harg : ((1 : ℝ) + (u : ℝ) / v) / (1 - (u : ℝ) / v)
        = ((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ) := by
      rw [Nat.cast_sub huv.le]; push_cast; field_simp
    rw [harg] at hm
    rw [hsumR]
    have habs : |Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ)) -
          2 * ∑ i ∈ Finset.range N, ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)|
        = 2 * |1 / 2 * Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ)) -
          ∑ i ∈ Finset.range N, ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)| := by
      rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← abs_mul]; congr 1; ring
    rw [habs]
    refine (mul_le_mul_of_nonneg_left hm (by norm_num)).trans ?_
    have hdm : ((u : ℝ) / v) ^ (2 * N + 1) / (1 - ((u : ℝ) / v) ^ 2)
        = ((u : ℝ) / v) ^ (2 * N + 1) * (1 - ((u : ℝ) / v) ^ 2)⁻¹ := div_eq_mul_inv _ _
    rw [abs_of_nonneg (by positivity), hdm]
    have hgf := geo_factor_le u v hv0 (by exact_mod_cast hg)
    have hA2 : (4 : ℝ) * ((u : ℝ) / v) ^ (2 * N + 1) ≤ 1 / (2 * D) := by
      rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (mul_pos two_pos hDr), one_mul]
      exact_mod_cast htail
    calc 2 * (((u : ℝ) / v) ^ (2 * N + 1) * (1 - ((u : ℝ) / v) ^ 2)⁻¹)
        ≤ 2 * (((u : ℝ) / v) ^ (2 * N + 1) * 2) := by gcongr
      _ = 4 * ((u : ℝ) / v) ^ (2 * N + 1) := by ring
      _ ≤ 1 / (2 * D) := hA2
  have h2val : 2 * ((u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd))
      = ((2 * (u * (Qd + T)) : ℕ) : ℝ) / ((v * Qd : ℕ) : ℝ) := by push_cast; ring
  have e1 : (p : ℝ) / Qdy ≤ ((2 * (u * (Qd + T)) : ℕ) : ℝ) / ((v * Qd : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hQdyr (by exact_mod_cast hden0)]; exact_mod_cast hr1
  have e2 : ((2 * (u * (Qd + T)) : ℕ) : ℝ) / ((v * Qd : ℕ) : ℝ) < (p : ℝ) / Qdy + 1 / Qdy := by
    rw [← add_div, div_lt_div_iff₀ (by exact_mod_cast hden0) hQdyr]; exact_mod_cast hr2
  have hround' : |2 * ((u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd)) - (p : ℝ) / Qdy|
      ≤ 1 / (2 * D) := by
    rw [h2val, abs_of_nonneg (sub_nonneg.mpr e1)]
    calc ((2 * (u * (Qd + T)) : ℕ) : ℝ) / ((v * Qd : ℕ) : ℝ) - (p : ℝ) / Qdy
        ≤ 1 / Qdy := by linarith [e2]
      _ ≤ 1 / (2 * D) := by
          rw [div_le_div_iff₀ hQdyr (mul_pos two_pos hDr), one_mul, one_mul]; exact_mod_cast hQ
  calc |Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ)) - (p : ℝ) / Qdy|
      ≤ |Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ))
            - 2 * ((u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd))|
          + |2 * ((u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd)) - (p : ℝ) / Qdy| := abs_sub_le _ _ _
    _ ≤ 1 / (2 * D) + 1 / (2 * D) := add_le_add hlog' hround'
    _ = 1 / D := by rw [← add_div, one_add_one_eq_two, ← div_div, div_self two_ne_zero]




theorem isNear_log_sfrac (pn pd cn cd rn rd : ℕ) (neg : Bool)
    (h : Real.IsNear (Real.log ((pn : ℝ) / pd)) neg cn cd rn rd) :
    Real.IsNear (Real.log (sfrac false pn pd)) neg cn cd rn rd := by rwa [sfrac_false_div]
















end BSN
end
end CertificatePort163


section CertificatePort165
section
namespace BSN
open Enclosure
theorem log2_combine (p₁ p₂ p₃ Q D E P : ℕ)
    (hD : Nat.ble 1 D) (hE : Nat.ble 1 E) (hDE : (Nat.mul 15 E).ble D)
    (hP : P.beq (((Nat.mul 7 p₁).add (Nat.mul 5 p₂)).add (Nat.mul 3 p₃)))
    (h₁ : Real.IsNear (Real.log (((32 : ℕ) : ℝ) / ((30 : ℕ) : ℝ))) false p₁ Q 1 D)
    (h₂ : Real.IsNear (Real.log (((50 : ℕ) : ℝ) / ((48 : ℕ) : ℝ))) false p₂ Q 1 D)
    (h₃ : Real.IsNear (Real.log (((162 : ℕ) : ℝ) / ((160 : ℕ) : ℝ))) false p₃ Q 1 D) :
    Real.IsNear (Real.log 2) false P Q 1 E := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at h₁ h₂ h₃ ⊢
  simp only [Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hDE hP
  subst hP
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  have e₁ : (((32 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = 16 / 15 := by norm_num
  have e₂ : (((50 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = 25 / 24 := by norm_num
  have e₃ : (((162 : ℕ) : ℝ) / ((160 : ℕ) : ℝ)) = 81 / 80 := by norm_num
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [e₃] at h₃
  have hdecomp : Real.log 2 = 7 * Real.log (16 / 15) + 5 * Real.log (25 / 24)
      + 3 * Real.log (81 / 80) := by
    have h2 : (2 : ℝ) = (16 / 15) ^ 7 * ((25 / 24) ^ 5 * (81 / 80) ^ 3) := by norm_num
    rw [h2, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have key : Real.log 2 - ((7 * p₁ + 5 * p₂ + 3 * p₃ : ℕ) : ℝ) / Q
      = 7 * (Real.log (16 / 15) - (p₁ : ℝ) / Q) + 5 * (Real.log (25 / 24) - (p₂ : ℝ) / Q)
        + 3 * (Real.log (81 / 80) - (p₃ : ℝ) / Q) := by
    rw [hdecomp]; push_cast; ring
  rw [key]
  calc |7 * (Real.log (16 / 15) - (p₁ : ℝ) / Q) + 5 * (Real.log (25 / 24) - (p₂ : ℝ) / Q)
          + 3 * (Real.log (81 / 80) - (p₃ : ℝ) / Q)|
      ≤ |7 * (Real.log (16 / 15) - (p₁ : ℝ) / Q)|
          + |5 * (Real.log (25 / 24) - (p₂ : ℝ) / Q)|
          + |3 * (Real.log (81 / 80) - (p₃ : ℝ) / Q)| := abs_add_three _ _ _
    _ = 7 * |Real.log (16 / 15) - (p₁ : ℝ) / Q| + 5 * |Real.log (25 / 24) - (p₂ : ℝ) / Q|
          + 3 * |Real.log (81 / 80) - (p₃ : ℝ) / Q| := by
        rw [abs_mul, abs_mul, abs_mul]; norm_num
    _ ≤ 7 * (1 / D) + 5 * (1 / D) + 3 * (1 / D) := by gcongr
    _ = 15 / D := by ring
    _ ≤ 1 / E := by rw [div_le_div_iff₀ hDr hEr, one_mul]; exact_mod_cast hDE
end BSN
end
end CertificatePort165
theorem BSN.log2_near_15._proof_1 : Enclosure.Real.IsNear
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast (nat_lit 32)) (@Nat.cast Real Real.instNatCast (nat_lit 30))))
  Bool.false (nat_lit 2325245277969667) (nat_lit 36028797018963968) (nat_lit 1) (nat_lit 15000000000000000) :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 31) (nat_lit 6) (nat_lit 5) (nat_lit 8520036043165426395)
  (nat_lit 36028797018963968) (nat_lit 15000000000000000) (nat_lit 2957113937425449) (nat_lit 945)
  (nat_lit 2325245277969667) (nat_lit 32) (nat_lit 30) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@BSN.binarySplit_of_base5 (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 31)) (nat_lit 0) (nat_lit 5)
    (nat_lit 2957113937425449) (nat_lit 8520036043165426395) (nat_lit 945) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.log2_near_15._proof_2 : Enclosure.Real.IsNear
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast (nat_lit 50)) (@Nat.cast Real Real.instNatCast (nat_lit 48))))
  Bool.false (nat_lit 1470767354479531) (nat_lit 36028797018963968) (nat_lit 1) (nat_lit 15000000000000000) :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 49) (nat_lit 5) (nat_lit 4) (nat_lit 31405119388272945)
  (nat_lit 36028797018963968) (nat_lit 15000000000000000) (nat_lit 4361095339944) (nat_lit 105)
  (nat_lit 1470767354479531) (nat_lit 50) (nat_lit 48) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@BSN.binarySplit_of_base4 (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 49)) (nat_lit 0) (nat_lit 4)
    (nat_lit 4361095339944) (nat_lit 31405119388272945) (nat_lit 105) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.log2_near_15._proof_3 : Enclosure.Real.IsNear
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast (nat_lit 162)) (@Nat.cast Real Real.instNatCast (nat_lit 160))))
  Bool.false (nat_lit 447568451492036) (nat_lit 36028797018963968) (nat_lit 1) (nat_lit 15000000000000000) :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 161) (nat_lit 4) (nat_lit 3) (nat_lit 1828708802020905)
  (nat_lit 36028797018963968) (nat_lit 15000000000000000) (nat_lit 23516982791) (nat_lit 15) (nat_lit 447568451492036)
  (nat_lit 162) (nat_lit 160) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@BSN.binarySplit_of_base3 (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 161)) (nat_lit 0) (nat_lit 3)
    (nat_lit 23516982791) (nat_lit 1828708802020905) (nat_lit 15) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.log2_near_15 : Enclosure.Real.IsNear
  (Real.log
    (@OfNat.ofNat Real (nat_lit 2)
      (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
  Bool.false (nat_lit 24973259072661432) (nat_lit 36028797018963968)
  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
  (@OfNat.ofNat Nat (nat_lit 1000000000000000) (instOfNatNat (nat_lit 1000000000000000))) :=
BSN.log2_combine (nat_lit 2325245277969667) (nat_lit 1470767354479531) (nat_lit 447568451492036)
  (nat_lit 36028797018963968) (nat_lit 15000000000000000) (nat_lit 1000000000000000) (nat_lit 24973259072661432)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  BSN.log2_near_15._proof_1 BSN.log2_near_15._proof_2 BSN.log2_near_15._proof_3


section CertificatePort167
section
namespace BSN
open Enclosure
theorem sqrt_enclosure (N M a b Q : ℕ)
    (hM : Nat.ble 1 M) (hQ : Nat.ble 1 Q) (hab : Nat.ble a b)
    (hlo : ((a.pow 2).mul M).ble (N.mul (Q.pow 2)))
    (hhi : (N.mul (Q.pow 2)).ble ((b.pow 2).mul M)) :
    Real.IsNear (Real.sqrt ((N : ℝ) / M)) false (a.add b) (Nat.mul 2 Q) (b.sub
          a) (Nat.mul 2 Q) := by
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  simp only [Nat.ble_eq, Nat.mul_eq, Nat.pow_eq] at hab hlo hhi
  have hMr : (0 : ℝ) < M := pos_real_of_ble hM
  have hQr : (0 : ℝ) < Q := pos_real_of_ble hQ
  have hQ2 : (0 : ℝ) < (Q : ℝ) ^ 2 := pow_pos hQr 2
  have hlo' : ((a : ℝ) / Q) ^ 2 ≤ (N : ℝ) / M := by
    rw [div_pow, div_le_div_iff₀ hQ2 hMr]; exact_mod_cast hlo
  have hhi' : (N : ℝ) / M ≤ ((b : ℝ) / Q) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hMr hQ2]; exact_mod_cast hhi
  have h1 : (a : ℝ) / Q ≤ Real.sqrt ((N : ℝ) / M) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (a : ℝ) / Q)]
    exact Real.sqrt_le_sqrt hlo'
  have h2 : Real.sqrt ((N : ℝ) / M) ≤ (b : ℝ) / Q := by
    calc Real.sqrt ((N : ℝ) / M)
        ≤ Real.sqrt (((b : ℝ) / Q) ^ 2) := Real.sqrt_le_sqrt hhi'
      _ = (b : ℝ) / Q := Real.sqrt_sq (by positivity)
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab
  have hc1 : ((a : ℝ) + b) / (2 * Q) - ((b : ℝ) - a) / (2 * Q) = (a : ℝ) / Q := by field_simp; ring
  have hc2 : ((a : ℝ) + b) / (2 * Q) + ((b : ℝ) - a) / (2 * Q) = (b : ℝ) / Q := by field_simp; ring
  rw [Real.IsNear, sfrac_false_div, abs_le]
  push_cast [hcast]
  exact ⟨by linarith [h1, hc1], by linarith [h2, hc2]⟩
end BSN
end
end CertificatePort167


section CertificatePort169
section
namespace BSN
open Enclosure
open Finset
private theorem prod_arctanEven (j : ℕ) :
    ∏ k ∈ range j, (4 * k + 5) = (∏ k ∈ range j, (4 * k + 1)) * (4 * j + 1) := by
  induction j with
  | zero => simp
  | succ n ih => rw [prod_range_succ, ih, prod_range_succ]; ring
private theorem prod_arctanOdd (j : ℕ) :
    (∏ k ∈ range j, (4 * k + 7)) * 3 = (∏ k ∈ range j, (4 * k + 3)) * (4 * j + 3) := by
  induction j with
  | zero => rfl
  | succ n ih => rw [prod_range_succ, prod_range_succ, ← ih]; ring
theorem arctan_sub_sum_le (x : ℝ) (M : ℕ) (hx : 0 ≤ x) (hx1 : x < 1) :
    |Real.arctan x - ∑ k ∈ range (2 * M), (-1) ^ k * x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)| ≤
      x ^ (4 * M + 1) / (4 * (M : ℝ) + 1) := by
  set f : ℕ → ℝ := fun n => x ^ (2 * n + 1) / (2 * (n : ℝ) + 1) with hf
  have hx2 : x ^ 2 < 1 := pow_lt_one₀ hx hx1 two_ne_zero
  have hanti : Antitone f := by
    intro a b hab
    simp only [hf]
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact div_le_div₀ (by positivity) (pow_le_pow_of_le_one hx hx1.le (by omega))
      (by positivity) (by linarith)
  have hsum : Summable f := by
    have hg : Summable (fun n : ℕ => x * (x ^ 2) ^ n) :=
      (summable_geometric_of_lt_one (sq_nonneg x) hx2).mul_left x
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hg
    simp only [hf]
    rw [show x * (x ^ 2) ^ n = x ^ (2 * n + 1) by rw [← pow_mul, ← pow_succ']]
    exact div_le_self (by positivity) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have harc : Real.arctan x = ∑' i, (-1) ^ i * f i := by
    rw [← (Real.hasSum_arctan (x := x)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hx]; exact hx1)).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [hf]
    rw [mul_div_assoc]
    push_cast
    ring
  have hbound := alternating_series_error_bound f hanti hsum (2 * M)
  rw [← harc] at hbound
  have hsumeq : (∑ i ∈ range (2 * M), (-1) ^ i * f i)
      = ∑ k ∈ range (2 * M), (-1) ^ k * x ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf]
    rw [mul_div_assoc]
  have hfeq : f (2 * M) = x ^ (4 * M + 1) / (4 * (M : ℝ) + 1) := by
    simp only [hf]
    rw [show 2 * (2 * M) + 1 = 4 * M + 1 by ring]
    push_cast
    ring
  rw [hsumeq, hfeq] at hbound
  exact hbound




theorem arctanEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((arctanEvenP u k : ℚ) / (arctanEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 1 : ℕ) : ℚ)) := by
  rw [← Finset.range_eq_Ico]
  simp only [arctanEvenP, arctanEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib]
  have hnum : (∏ k ∈ Finset.range (i + 1), ((u ^ 4 * (4 * k + 1) : ℕ) : ℚ))
      = (u : ℚ) ^ (4 * (i + 1)) * ∏ k ∈ Finset.range (i + 1), ((4 * k + 1 : ℕ) : ℚ) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hden : (∏ k ∈ Finset.range (i + 1), ((v ^ 4 * (4 * k + 5) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), ((4 * k + 1 : ℕ) : ℚ))
        * (4 * (i + 1) + 1)) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
    congr 1
    exact_mod_cast prod_arctanEven (i + 1)
  rw [hnum, hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hp1 : (∏ k ∈ Finset.range (i + 1), ((4 * k + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp
theorem arctanEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (arctanEvenP u) (arctanEvenQ v) 0 (M - 1)) :
    ((u : ℚ) * (Q + T) / (v * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 1) / ((v : ℚ) ^ (4 * j + 1) * ((4 * j + 1 : ℕ) : ℚ)) := by
  have hqne : ∀ i, arctanEvenQ v i ≠ 0 := by
    intro i; simp only [arctanEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb :=
        binarySplit_nonzero (p := arctanEvenP u) (q := arctanEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := arctanEvenP u) (q := arctanEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => arctanEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 1) / ((v : ℚ) ^ (4 * (i + 1) + 1) * ((4 * (i + 1) + 1 : ℕ) : ℚ))
        = (u : ℚ) / v *
          ((u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 1 : ℕ) : ℚ))) := by
    intro i _
    rw [pow_succ' (u : ℚ), pow_succ' (v : ℚ)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.cast_one, mul_one]
  field_simp
  ring
theorem arctanOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((arctanOddP u k : ℚ) / (arctanOddQ v k))
      = 3 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 3 : ℕ) : ℚ)) := by
  rw [← Finset.range_eq_Ico]
  simp only [arctanOddP, arctanOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib]
  have hnum : (∏ k ∈ Finset.range (i + 1), ((u ^ 4 * (4 * k + 3) : ℕ) : ℚ))
      = (u : ℚ) ^ (4 * (i + 1)) * ∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hden : (∏ k ∈ Finset.range (i + 1), ((v ^ 4 * (4 * k + 7) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ))
        * (4 * (i + 1) + 3)) / 3 := by
    have keyN : (∏ k ∈ Finset.range (i + 1), (v ^ 4 * (4 * k + 7))) * 3
        = v ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), (4 * k + 3)) * (4 * (i + 1) + 3)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_arctanOdd]
    have keyQ : (∏ k ∈ Finset.range (i + 1), ((v ^ 4 * (4 * k + 7) : ℕ) : ℚ)) * 3
        = (v : ℚ) ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ))
          * (4 * (i + 1) + 3)) := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)]
  rw [hnum, hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hp1 : (∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp
theorem arctanOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (arctanOddP u) (arctanOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 3 * (Q + T) / (3 * v ^ 3 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 3) / ((v : ℚ) ^ (4 * j + 3) * ((4 * j + 3 : ℕ) : ℚ)) := by
  have hqne : ∀ i, arctanOddQ v i ≠ 0 := by
    intro i; simp only [arctanOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb :=
        binarySplit_nonzero (p := arctanOddP u) (q := arctanOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := arctanOddP u) (q := arctanOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => arctanOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 3) / ((v : ℚ) ^ (4 * (i + 1) + 3) * ((4 * (i + 1) + 3 : ℕ) : ℚ))
        = (u : ℚ) ^ 3 / (3 * v ^ 3) *
          (3 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 3 : ℕ) : ℚ))) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 3, pow_add (v : ℚ) (4 * (i + 1)) 3]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add]
  push_cast
  field_simp
  ring
theorem arctan_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (huv : u.blt v) (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hM : Nat.ble 1 M) (hMm : (Mm.succ).beq M)
    (heven : binarySplit (arctanEvenP u) (arctanEvenQ v) 0 Mm = (Te, Qe, Pe))
    (hodd : binarySplit (arctanOddP u) (arctanOddQ v) 0 Mm = (To, Qo, Po))
    (htail : ((u.pow ((Nat.mul 4 M).succ)).mul (Nat.mul 2 D)).ble
      ((v.pow ((Nat.mul 4 M).succ)).mul ((Nat.mul 4 M).succ)))
    (hr1 : (((numPos neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.arctan ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQeN : 0 < Qe := pos_of_ble hQe
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := arctanEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := arctanOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : (u : ℚ) * (Qe + Te) / (v * Qe) - (u : ℚ) ^ 3 * (Qo + To) / (3 * v ^ 3 * Qo)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℚ) / v) ^ (2 * i + 1) / (2 * (i : ℚ) + 1) := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) + 1 = 4 * j + 1 := by ring
    have e2 : 2 * (2 * j + 1) + 1 = 4 * j + 3 := by ring
    rw [e1, e2, s1, s2]
    push_cast
    rw [div_pow, div_pow]
    have d1 : (2 : ℚ) * (2 * (j : ℚ)) + 1 = 4 * (j : ℚ) + 1 := by ring
    have d2 : (2 : ℚ) * (2 * (j : ℚ) + 1) + 1 = 4 * (j : ℚ) + 3 := by ring
    rw [d1, d2]
    field_simp
    ring
  set m : ℤ := (mp : ℤ) - (mn : ℤ) with hm
  rw [Real.IsNear, Nat.cast_one]
  have hvform : sfrac neg cn Q = (m : ℝ) / Q := by
    rw [sfrac_eq_parts neg cn Q, ← hmp_def, ← hmn_def, hm]
    push_cast
    ring
  rw [hvform]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at huv htail hQ hr1 hr2
  set De := v * Qe with hDe_def
  set Do := 3 * v ^ 3 * Qo with hDo_def
  set Ne := u * (Qe + Te) with hNe_def
  set No := u ^ 3 * (Qo + To) with hNo_def
  have hDeR : (De : ℝ) = (v : ℝ) * Qe := by rw [hDe_def]; push_cast; ring
  have hDoR : (Do : ℝ) = 3 * (v : ℝ) ^ 3 * Qo := by rw [hDo_def]; push_cast; ring
  have hr1z : m * ((De : ℤ) * Do) ≤ ((Ne : ℤ) * Do - (No : ℤ) * De) * Q := by
    have h : (mp : ℤ) * ((De : ℤ) * Do) + (No : ℤ) * De * Q
        ≤ (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do) := by exact_mod_cast hr1
    have e1 : m * ((De : ℤ) * Do) = (mp : ℤ) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by
      rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hr2z : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q < (m + 1) * ((De : ℤ) * Do) := by
    have h : (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do)
        < (mp + 1) * ((De : ℤ) * Do) + (No : ℤ) * De * Q := by exact_mod_cast hr2
    have e1 : (m + 1) * ((De : ℤ) * Do)
        = (mp + 1) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hDe0 : (0 : ℝ) < De := by rw [hDeR]; positivity
  have hDo0 : (0 : ℝ) < Do := by rw [hDoR]; positivity
  have hvalR : ((Ne : ℝ) / De - (No : ℝ) / Do)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDe_def, hNo_def, hDo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 1 := by rw [div_lt_one hvr]; exact_mod_cast huv
  have harem := arctan_sub_sum_le ((u : ℝ) / v) M hxnn hxlt
  rw [← hvalR] at harem
  have hatail : |Real.arctan ((u : ℝ) / v) - ((Ne : ℝ) / De - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine harem.trans ?_
    rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have e : (4 * (M : ℝ) + 1) = ((4 * M + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    exact_mod_cast htail
  have hr1' : (m : ℝ) * ((De : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * De) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * De) * Q < ((m : ℝ) + 1) * ((De : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.arctan ((u : ℝ) / v)) (Ne : ℝ) (De : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hatail hr1' hr2' hDe0 hDo0 hDr hQr hQ
theorem arctan_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (huv : u.blt v) (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hM : Nat.ble 1 M) (hMm : (Mm.succ).beq M)
    (heven : binarySplit (arctanEvenP u) (arctanEvenQ v) 0 Mm = (Te, Qe, Pe))
    (hodd : binarySplit (arctanOddP u) (arctanOddQ v) 0 Mm = (To, Qo, Po))
    (htail : ((u.pow ((Nat.mul 4 M).succ)).mul (Nat.mul 2 D)).ble
      ((v.pow ((Nat.mul 4 M).succ)).mul ((Nat.mul 4 M).succ)))
    (hr1 : ((cn.mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      (((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q)).blt
      (((cn.succ).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.arctan ((u : ℝ) / v)) false cn Q 1 D := by
  refine arctan_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn huv hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega


end BSN
end
end CertificatePort169


section CertificatePort170
section
namespace BSN
open Enclosure
theorem pi_combine (c₁ c₂ Q D E P : ℕ)
    (hD : Nat.ble 1 D) (hE : Nat.ble 1 E) (hDE : (Nat.mul 20 E).ble D)
    (hP : (P.add (Nat.mul 4 c₂)).beq (Nat.mul 16 c₁))
    (h₁ : Real.IsNear (Real.arctan (((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))) false c₁ Q 1 D)
    (h₂ : Real.IsNear (Real.arctan (((1 : ℕ) : ℝ) / ((239 : ℕ) : ℝ))) false c₂ Q 1 D) :
    Real.IsNear Real.pi false P Q 1 E := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at h₁ h₂ ⊢
  simp only [Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hDE hP
  have harg5 : ((1 : ℝ) / ((5 : ℕ) : ℝ)) = 5⁻¹ := by norm_num
  have harg239 : ((1 : ℝ) / ((239 : ℕ) : ℝ)) = 239⁻¹ := by norm_num
  rw [harg5] at h₁
  rw [harg239] at h₂
  have hmachin : Real.pi = 16 * Real.arctan 5⁻¹ - 4 * Real.arctan 239⁻¹ := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    linarith
  have hPr : (P : ℝ) = 16 * c₁ - 4 * c₂ := by
    have h : (P : ℝ) + 4 * c₂ = 16 * c₁ := by exact_mod_cast hP
    linarith
  have key : Real.pi - (P : ℝ) / Q
      = 16 * (Real.arctan 5⁻¹ - (c₁ : ℝ) / Q)
        - 4 * (Real.arctan 239⁻¹ - (c₂ : ℝ) / Q) := by
    rw [hmachin, hPr]; ring
  rw [key]
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  calc |16 * (Real.arctan 5⁻¹ - (c₁ : ℝ) / Q)
          - 4 * (Real.arctan 239⁻¹ - (c₂ : ℝ) / Q)|
      ≤ |16 * (Real.arctan 5⁻¹ - (c₁ : ℝ) / Q)|
          + |4 * (Real.arctan 239⁻¹ - (c₂ : ℝ) / Q)| := by
        exact abs_sub _ _
    _ = 16 * |Real.arctan 5⁻¹ - (c₁ : ℝ) / Q|
          + 4 * |Real.arctan 239⁻¹ - (c₂ : ℝ) / Q| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ 16 * (1 / D) + 4 * (1 / D) := by gcongr
    _ = 20 / D := by ring
    _ ≤ 1 / E := by rw [div_le_div_iff₀ hDr hEr, one_mul]; exact_mod_cast hDE
end BSN
end
end CertificatePort170
theorem BSN.pi_near_15._proof_1 : Enclosure.Real.IsNear
  (Real.arctan
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast (nat_lit 1)) (@Nat.cast Real Real.instNatCast (nat_lit 5))))
  Bool.false (nat_lit 14223849116552214) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 20000000000000000) :=
BSN.arctan_dyadic_bound_f (nat_lit 1) (nat_lit 5) (nat_lit 6) (nat_lit 5) (nat_lit 72057594037927936)
  (nat_lit 20000000000000000) (nat_lit 6379115169797445) (nat_lit 19917011260986328125) (nat_lit 9945)
  (nat_lit 33040696220578335) (nat_lit 48135280609130859375) (nat_lit 65835) (nat_lit 14223849116552214)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@BSN.binarySplit_of_base5 (BSN.arctanEvenP (nat_lit 1)) (BSN.arctanEvenQ (nat_lit 5)) (nat_lit 0) (nat_lit 5)
    (nat_lit 6379115169797445) (nat_lit 19917011260986328125) (nat_lit 9945) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@BSN.binarySplit_of_base5 (BSN.arctanOddP (nat_lit 1)) (BSN.arctanOddQ (nat_lit 5)) (nat_lit 0) (nat_lit 5)
    (nat_lit 33040696220578335) (nat_lit 48135280609130859375) (nat_lit 65835) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.pi_near_15._proof_2 : Enclosure.Real.IsNear
  (Real.arctan
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast (nat_lit 1)) (@Nat.cast Real Real.instNatCast (nat_lit 239))))
  Bool.false (nat_lit 301494449981336) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 20000000000000000) :=
BSN.arctan_dyadic_bound_f (nat_lit 1) (nat_lit 239) (nat_lit 2) (nat_lit 1) (nat_lit 72057594037927936)
  (nat_lit 20000000000000000) (nat_lit 1) (nat_lit 16314043205) (nat_lit 1) (nat_lit 3) (nat_lit 22839660487)
  (nat_lit 3) (nat_lit 301494449981336) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@BSN.binarySplit_of_base (BSN.arctanEvenP (nat_lit 1)) (BSN.arctanEvenQ (nat_lit 239)) (nat_lit 0) (nat_lit 1)
    (nat_lit 1) (nat_lit 16314043205) (nat_lit 1) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@BSN.binarySplit_of_base (BSN.arctanOddP (nat_lit 1)) (BSN.arctanOddQ (nat_lit 239)) (nat_lit 0) (nat_lit 1)
    (nat_lit 3) (nat_lit 22839660487) (nat_lit 3) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.pi_near_15 : Enclosure.Real.IsNear Real.pi Bool.false (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 1000000000000000) :=
BSN.pi_combine (nat_lit 14223849116552214) (nat_lit 301494449981336) (nat_lit 72057594037927936)
  (nat_lit 20000000000000000) (nat_lit 1000000000000000) (nat_lit 226375608064910080) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) BSN.pi_near_15._proof_1
  BSN.pi_near_15._proof_2


section CertificatePort173
section
namespace BSN
open Enclosure










end BSN
end
end CertificatePort173
section Reduced182
section
namespace Zeta.Certificates.Gram
open Zeta.Certificates Real Set


end Zeta.Certificates.Gram
end
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace BSN
theorem sqrt_natCast_div_one (n : ℕ) :
    Real.sqrt (n : ℝ) = Real.sqrt ((n : ℝ) / ((nat_lit 1 : ℕ) : ℝ)) := by
  rw [show ((nat_lit 1 : ℕ) : ℝ) = 1 from Nat.cast_one, div_one]
end BSN
namespace Zeta.Certificates.Gram
open Zeta.Certificates Real Set


end Zeta.Certificates.Gram
end Reduced182

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false
set_option linter.auxLemma false
open scoped BigOperators

namespace RHHeight1000.EMHead24At48711
noncomputable def p31198 :=
@Enclosure.Complex.IsNear.mk (Enclosure.sfrac false (nat_lit 1) (nat_lit 1))
  (Enclosure.sfrac false (nat_lit 0) (nat_lit 1)) false (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1)
  false

noncomputable def p31204 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2)))) false
  (nat_lit 741455) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31205 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2))) (nat_lit 1482911)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 370727) (nat_lit 370728)

noncomputable def p31206 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 1482911) (nat_lit 1048576)

noncomputable def p31207 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 1482911) (nat_lit 1048576)

noncomputable def p31208 :=
@p31207 (nat_lit 1) (nat_lit 1048576) (nat_lit 1482911) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 2) (nat_lit 1) (nat_lit 741455) (nat_lit 741456) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31209 :=
@p31205 (nat_lit 524288)
  (@p31206 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 2))
    (p31208 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31213 :=
BSN.logfrac_isNear (nat_lit 4) (nat_lit 2) (nat_lit 1) (nat_lit 2) (nat_lit 1) (nat_lit 363408) (nat_lit 524288)
  (nat_lit 200000) (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31214 :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 3) (nat_lit 7) (nat_lit 6) (nat_lit 71816279535) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 2852596872) (nat_lit 10395) (nat_lit 363408) (nat_lit 4)

noncomputable def p31215 :=
p31214 (nat_lit 2) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31216 :=
@BSN.binarySplit_of_base6 (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 3)) (nat_lit 0) (nat_lit 6)
  (nat_lit 2852596872) (nat_lit 71816279535) (nat_lit 10395) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31249 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3)))) false
  (nat_lit 605395) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31250 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3))) (nat_lit 1816187)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 302697) (nat_lit 302698)

noncomputable def p31251 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 1816187) (nat_lit 1048576)

noncomputable def p31252 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 1816187) (nat_lit 1048576)

noncomputable def p31253 :=
@p31252 (nat_lit 1) (nat_lit 1048576) (nat_lit 1816187) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 3) (nat_lit 1) (nat_lit 908093) (nat_lit 908094) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31254 :=
@p31250 (nat_lit 524288)
  (@p31251 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 3))
    (p31253 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31258 :=
BSN.logfrac_isNear (nat_lit 3) (nat_lit 1) (nat_lit 2) (nat_lit 3) (nat_lit 1) (nat_lit 575989) (nat_lit 524288)
  (nat_lit 200000) (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31259 :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 2) (nat_lit 10) (nat_lit 9) (nat_lit 171633298636800) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 16925142283965) (nat_lit 34459425) (nat_lit 575989) (nat_lit 3)

noncomputable def p31260 :=
p31259 (nat_lit 1) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31261 :=
@BSN.binarySplit_of_base9 (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 2)) (nat_lit 0) (nat_lit 9)
  (nat_lit 16925142283965) (nat_lit 171633298636800) (nat_lit 34459425) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p31297 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4)))) false
  (nat_lit 524287) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31298 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4))) (nat_lit 2097153)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 262143) (nat_lit 262144)

noncomputable def p31299 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 2097153) (nat_lit 1048576)

noncomputable def p31300 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 2097153) (nat_lit 1048576)

noncomputable def p31301 :=
@p31300 (nat_lit 1) (nat_lit 1048576) (nat_lit 2097153) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 4) (nat_lit 1) (nat_lit 1048576) (nat_lit 1048577) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31302 :=
@p31298 (nat_lit 524288)
  (@p31299 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 4))
    (p31301 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31306 :=
BSN.logfrac_isNear (nat_lit 8) (nat_lit 2) (nat_lit 1) (nat_lit 4) (nat_lit 1) (nat_lit 726817) (nat_lit 524288)
  (nat_lit 200000) (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31307 :=
nat_lit 318077276165597140789031982421875

noncomputable def p31308 :=
nat_lit 49379992292270016474244603430625

noncomputable def p31309 :=
nat_lit 20095619060363156210525625

noncomputable def p31310 :=
BSN.log_dyadic_bound (nat_lit 3) (nat_lit 5) (nat_lit 14) (nat_lit 13) p31307 (nat_lit 524288)
  (nat_lit 200000) p31308 p31309 (nat_lit 726817) (nat_lit 8)

noncomputable def p31311 :=
p31310 (nat_lit 2) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31312 :=
@BSN.binarySplit_of_base13 (BSN.artanhP (nat_lit 3)) (BSN.artanhQ (nat_lit 5)) (nat_lit 0) (nat_lit 13)
  p31308 p31307 p31309 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p31345 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5)))) false
  (nat_lit 468937) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31346 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5))) (nat_lit 2344687)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 234468) (nat_lit 234469)

noncomputable def p31347 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 2344687) (nat_lit 1048576)

noncomputable def p31348 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 2344687) (nat_lit 1048576)

noncomputable def p31349 :=
@p31348 (nat_lit 1) (nat_lit 1048576) (nat_lit 2344687) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 5) (nat_lit 1) (nat_lit 1172343) (nat_lit 1172344) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31350 :=
@p31346 (nat_lit 524288)
  (@p31347 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 5))
    (p31349 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31354 :=
BSN.logfrac_isNear (nat_lit 5) (nat_lit 1) (nat_lit 2) (nat_lit 5) (nat_lit 1) (nat_lit 843808) (nat_lit 524288)
  (nat_lit 200000) (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31355 :=
nat_lit 3696382175741467532940033205863946875

noncomputable def p31356 :=
nat_lit 765440954430599474856563326857688500

noncomputable def p31357 :=
nat_lit 108794268166472120024432640000

noncomputable def p31358 :=
BSN.log_dyadic_bound (nat_lit 2) (nat_lit 3) (nat_lit 18) (nat_lit 17) p31355 (nat_lit 524288)
  (nat_lit 200000) p31356 p31357 (nat_lit 843808) (nat_lit 5)

noncomputable def p31359 :=
p31358 (nat_lit 1) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31360 :=
@BSN.binarySplit_rec (BSN.artanhP (nat_lit 2)) (BSN.artanhQ (nat_lit 3)) (nat_lit 0) (nat_lit 17) (nat_lit 8)
  (nat_lit 307084260767580) (nat_lit 1483365253795425) (nat_lit 132843110400) (nat_lit 1663129201793174588340)
  (nat_lit 2491889415829100854875)

noncomputable def p31361 :=
@BSN.binarySplit_of_base8 (BSN.artanhP (nat_lit 2)) (BSN.artanhQ (nat_lit 3)) (nat_lit 0) (nat_lit 8)
  (nat_lit 307084260767580) (nat_lit 1483365253795425) (nat_lit 132843110400) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p31362 :=
@BSN.binarySplit_of_base9 (BSN.artanhP (nat_lit 2)) (BSN.artanhQ (nat_lit 3)) (nat_lit 8) (nat_lit 17)
  (nat_lit 1663129201793174588340) (nat_lit 2491889415829100854875) (nat_lit 818968088287641600)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31363 :=
@p31360 (nat_lit 818968088287641600) p31356 p31355
  p31357 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (p31361 (Eq.refl true))
  (p31362 (Eq.refl true))

noncomputable def p31401 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6)))) false
  (nat_lit 428079) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31402 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6))) (nat_lit 2568477)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 214039) (nat_lit 214040)

noncomputable def p31403 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 2568477) (nat_lit 1048576)

noncomputable def p31404 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 2568477) (nat_lit 1048576)

noncomputable def p31405 :=
@p31404 (nat_lit 1) (nat_lit 1048576) (nat_lit 2568477) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 6) (nat_lit 1) (nat_lit 1284238) (nat_lit 1284239) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31406 :=
@p31402 (nat_lit 524288)
  (@p31403 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 6))
    (p31405 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31411 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 33845361775666394038272) (nat_lit 18889465931478580854784)

noncomputable def p31412 :=
BSN.log_rat_reduce_isNear (nat_lit 6) (nat_lit 1) (nat_lit 2) (nat_lit 12) (nat_lit 8) (nat_lit 212580) (nat_lit 524288)
  (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31413 :=
BSN.log_dyadic_bound (nat_lit 2) (nat_lit 10) (nat_lit 4) (nat_lit 3) (nat_lit 105000000) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 1434560) (nat_lit 960) (nat_lit 212580) (nat_lit 12)

noncomputable def p31414 :=
p31413 (nat_lit 8) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31415 :=
@BSN.binarySplit_of_base3 (BSN.artanhP (nat_lit 2)) (BSN.artanhQ (nat_lit 10)) (nat_lit 0) (nat_lit 3) (nat_lit 1434560)
  (nat_lit 105000000) (nat_lit 960) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31416 :=
p31412 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p31414 (p31415 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p31452 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7)))) false
  (nat_lit 396325) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31453 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7))) (nat_lit 2774271)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 198162) (nat_lit 198163)

noncomputable def p31454 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 2774271) (nat_lit 1048576)

noncomputable def p31455 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 2774271) (nat_lit 1048576)

noncomputable def p31456 :=
@p31455 (nat_lit 1) (nat_lit 1048576) (nat_lit 2774271) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 7) (nat_lit 1) (nat_lit 1387135) (nat_lit 1387136) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31457 :=
@p31453 (nat_lit 524288)
  (@p31454 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 7))
    (p31456 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31462 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 36757173121942042968064) (nat_lit 18889465931478580854784)

noncomputable def p31463 :=
BSN.log_rat_reduce_isNear (nat_lit 7) (nat_lit 1) (nat_lit 2) (nat_lit 14) (nat_lit 8) (nat_lit 293399) (nat_lit 524288)
  (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31464 :=
BSN.log_dyadic_bound (nat_lit 3) (nat_lit 11) (nat_lit 5) (nat_lit 4) (nat_lit 202569142545) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 5259111624) (nat_lit 688905) (nat_lit 293399) (nat_lit 14)

noncomputable def p31465 :=
p31464 (nat_lit 8) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31466 :=
@BSN.binarySplit_of_base4 (BSN.artanhP (nat_lit 3)) (BSN.artanhQ (nat_lit 11)) (nat_lit 0) (nat_lit 4)
  (nat_lit 5259111624) (nat_lit 202569142545) (nat_lit 688905) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p31467 :=
p31463 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p31465 (p31466 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p31505 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8)))) false
  (nat_lit 370727) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31506 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8))) (nat_lit 2965821)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 185363) (nat_lit 185364)

noncomputable def p31507 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 2965821) (nat_lit 1048576)

noncomputable def p31508 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 2965821) (nat_lit 1048576)

noncomputable def p31509 :=
@p31508 (nat_lit 1) (nat_lit 1048576) (nat_lit 2965821) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 8) (nat_lit 1) (nat_lit 1482910) (nat_lit 1482911) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31510 :=
@p31506 (nat_lit 524288)
  (@p31507 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 8))
    (p31509 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31515 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 39279540158062550581248) (nat_lit 18889465931478580854784)

noncomputable def p31516 :=
BSN.log_rat_reduce_isNear (nat_lit 8) (nat_lit 1) (nat_lit 3) (nat_lit 16) (nat_lit 16) (nat_lit 0) (nat_lit 524288)
  (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31517 :=
BSN.log_dyadic_bound (nat_lit 0) (nat_lit 16) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 524288) (nat_lit 200000)
  (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 16)

noncomputable def p31518 :=
p31517 (nat_lit 16) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31519 :=
p31518
  (@BSN.binarySplit_of_le (BSN.artanhP (nat_lit 0)) (BSN.artanhQ (nat_lit 16)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31520 :=
p31516 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) p31519 BSN.log2_near_15 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p31525 :=
nat_lit 2552117751907038475975309555738261585920

noncomputable def p31526 :=
nat_lit 17864824263349269331827166890167831101440

noncomputable def p31541 :=
nat_lit 510423550381407695195061911147652317184

noncomputable def p31542 :=
nat_lit 7656353255721115427925928667214784757760

noncomputable def p31596 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9)))) false
  (nat_lit 349525) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31597 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9))) (nat_lit 3145729)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 174762) (nat_lit 174763)

noncomputable def p31598 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3145729) (nat_lit 1048576)

noncomputable def p31599 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3145729) (nat_lit 1048576)

noncomputable def p31600 :=
@p31599 (nat_lit 1) (nat_lit 1048576) (nat_lit 3145729) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 9) (nat_lit 1) (nat_lit 1572864) (nat_lit 1572865) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31601 :=
@p31597 (nat_lit 524288)
  (@p31598 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 9))
    (p31600 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31606 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 41504390431577613533184) (nat_lit 18889465931478580854784)

noncomputable def p31607 :=
BSN.log_rat_reduce_isNear (nat_lit 9) (nat_lit 1) (nat_lit 3) (nat_lit 18) (nat_lit 16) (nat_lit 61752) (nat_lit 524288)
  (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31608 :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 17) (nat_lit 3) (nat_lit 2) (nat_lit 1252815) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 1448) (nat_lit 3) (nat_lit 61752) (nat_lit 18)

noncomputable def p31609 :=
p31608 (nat_lit 16) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31610 :=
@BSN.binarySplit_of_base2 (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 17)) (nat_lit 0) (nat_lit 2) (nat_lit 1448)
  (nat_lit 1252815) (nat_lit 3) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31611 :=
p31607 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p31609 (p31610 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p31646 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10)))) false
  (nat_lit 331589) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31647 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10))) (nat_lit 3315889)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 165794) (nat_lit 165795)

noncomputable def p31648 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3315889) (nat_lit 1048576)

noncomputable def p31649 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3315889) (nat_lit 1048576)

noncomputable def p31650 :=
@p31649 (nat_lit 1) (nat_lit 1048576) (nat_lit 3315889) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 10) (nat_lit 1) (nat_lit 1657944) (nat_lit 1657945) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31651 :=
@p31647 (nat_lit 524288)
  (@p31648 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 10))
    (p31650 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31656 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 43494585150108164161536) (nat_lit 18889465931478580854784)

noncomputable def p31657 :=
BSN.log_rat_reduce_isNear (nat_lit 10) (nat_lit 1) (nat_lit 3) (nat_lit 20) (nat_lit 16) (nat_lit 116991)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31658 :=
BSN.log_dyadic_bound (nat_lit 2) (nat_lit 18) (nat_lit 3) (nat_lit 2) (nat_lit 1574640) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 6528) (nat_lit 48) (nat_lit 116991) (nat_lit 20)

noncomputable def p31659 :=
p31658 (nat_lit 16) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31660 :=
@BSN.binarySplit_of_base2 (BSN.artanhP (nat_lit 2)) (BSN.artanhQ (nat_lit 18)) (nat_lit 0) (nat_lit 2) (nat_lit 6528)
  (nat_lit 1574640) (nat_lit 48) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31661 :=
p31657 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p31659 (p31660 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p31681 :=
nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def p31684 :=
nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def p31702 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11)))) false
  (nat_lit 316157) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31703 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11))) (nat_lit 3477733)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 158078) (nat_lit 158079)

noncomputable def p31704 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3477733) (nat_lit 1048576)

noncomputable def p31705 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3477733) (nat_lit 1048576)

noncomputable def p31706 :=
@p31705 (nat_lit 1) (nat_lit 1048576) (nat_lit 3477733) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 11) (nat_lit 1) (nat_lit 1738866) (nat_lit 1738867) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31707 :=
@p31703 (nat_lit 524288)
  (@p31704 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 11))
    (p31706 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31712 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 45294944137145793642496) (nat_lit 18889465931478580854784)

noncomputable def p31713 :=
BSN.log_rat_reduce_isNear (nat_lit 11) (nat_lit 1) (nat_lit 3) (nat_lit 22) (nat_lit 16) (nat_lit 166961)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31714 :=
BSN.log_dyadic_bound (nat_lit 3) (nat_lit 19) (nat_lit 4) (nat_lit 3) (nat_lit 4939817505) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 41676111) (nat_lit 10935) (nat_lit 166961) (nat_lit 22)

noncomputable def p31715 :=
p31714 (nat_lit 16) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31716 :=
@BSN.binarySplit_of_base3 (BSN.artanhP (nat_lit 3)) (BSN.artanhQ (nat_lit 19)) (nat_lit 0) (nat_lit 3)
  (nat_lit 41676111) (nat_lit 4939817505) (nat_lit 10935) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31717 :=
p31713 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p31715 (p31716 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p31756 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12)))) false
  (nat_lit 302697) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31757 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12))) (nat_lit 3632373)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 151348) (nat_lit 151349)

noncomputable def p31758 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3632373) (nat_lit 1048576)

noncomputable def p31759 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3632373) (nat_lit 1048576)

noncomputable def p31760 :=
@p31759 (nat_lit 1) (nat_lit 1048576) (nat_lit 3632373) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 12) (nat_lit 1) (nat_lit 1816186) (nat_lit 1816187) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31761 :=
@p31757 (nat_lit 524288)
  (@p31758 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 12))
    (p31760 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31766 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 46938541828353910898688) (nat_lit 18889465931478580854784)

noncomputable def p31767 :=
BSN.log_rat_reduce_isNear (nat_lit 12) (nat_lit 1) (nat_lit 3) (nat_lit 24) (nat_lit 16) (nat_lit 212580)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31768 :=
BSN.log_dyadic_bound (nat_lit 4) (nat_lit 20) (nat_lit 4) (nat_lit 3) (nat_lit 6720000000) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 91811840) (nat_lit 61440) (nat_lit 212580) (nat_lit 24)

noncomputable def p31769 :=
p31768 (nat_lit 16) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31770 :=
@BSN.binarySplit_of_base3 (BSN.artanhP (nat_lit 4)) (BSN.artanhQ (nat_lit 20)) (nat_lit 0) (nat_lit 3)
  (nat_lit 91811840) (nat_lit 6720000000) (nat_lit 61440) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31771 :=
p31767 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p31769 (p31770 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p31776 :=
nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def p31779 :=
nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def p31813 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13)))) false
  (nat_lit 290823) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31814 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13))) (nat_lit 3780695)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 145411) (nat_lit 145412)

noncomputable def p31815 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3780695) (nat_lit 1048576)

noncomputable def p31816 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3780695) (nat_lit 1048576)

noncomputable def p31817 :=
@p31816 (nat_lit 1) (nat_lit 1048576) (nat_lit 3780695) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 13) (nat_lit 1) (nat_lit 1890347) (nat_lit 1890348) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31818 :=
@p31814 (nat_lit 524288)
  (@p31815 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 13))
    (p31817 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31823 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 48450490295254733815808) (nat_lit 18889465931478580854784)

noncomputable def p31824 :=
BSN.log_rat_reduce_isNear (nat_lit 13) (nat_lit 1) (nat_lit 3) (nat_lit 26) (nat_lit 16) (nat_lit 254545)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31825 :=
BSN.log_dyadic_bound (nat_lit 5) (nat_lit 21) (nat_lit 5) (nat_lit 4) (nat_lit 35742602096145) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 699352521000) (nat_lit 41015625) (nat_lit 254545) (nat_lit 26)

noncomputable def p31826 :=
p31825 (nat_lit 16) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31827 :=
@BSN.binarySplit_of_base4 (BSN.artanhP (nat_lit 5)) (BSN.artanhQ (nat_lit 21)) (nat_lit 0) (nat_lit 4)
  (nat_lit 699352521000) (nat_lit 35742602096145) (nat_lit 41015625) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p31828 :=
p31824 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p31826 (p31827 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p31868 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14)))) false
  (nat_lit 280243) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31869 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14))) (nat_lit 3923413)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 140121) (nat_lit 140122)

noncomputable def p31870 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3923413) (nat_lit 1048576)

noncomputable def p31871 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 3923413) (nat_lit 1048576)

noncomputable def p31872 :=
@p31871 (nat_lit 1) (nat_lit 1048576) (nat_lit 3923413) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 14) (nat_lit 1) (nat_lit 1961706) (nat_lit 1961707) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31873 :=
@p31869 (nat_lit 524288)
  (@p31870 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 14))
    (p31872 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31878 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 49850353174629559828480) (nat_lit 18889465931478580854784)

noncomputable def p31879 :=
BSN.log_rat_reduce_isNear (nat_lit 14) (nat_lit 1) (nat_lit 3) (nat_lit 28) (nat_lit 16) (nat_lit 293399)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31880 :=
BSN.log_dyadic_bound (nat_lit 6) (nat_lit 22) (nat_lit 5) (nat_lit 4) (nat_lit 51857700491520) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 1346332575744) (nat_lit 176359680) (nat_lit 293399) (nat_lit 28)

noncomputable def p31881 :=
p31880 (nat_lit 16) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31882 :=
@BSN.binarySplit_of_base4 (BSN.artanhP (nat_lit 6)) (BSN.artanhQ (nat_lit 22)) (nat_lit 0) (nat_lit 4)
  (nat_lit 1346332575744) (nat_lit 51857700491520) (nat_lit 176359680) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p31883 :=
p31879 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p31881 (p31882 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p31923 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15)))) false
  (nat_lit 270741) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31924 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15))) (nat_lit 4061117)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 135370) (nat_lit 135371)

noncomputable def p31925 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4061117) (nat_lit 1048576)

noncomputable def p31926 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4061117) (nat_lit 1048576)

noncomputable def p31927 :=
@p31926 (nat_lit 1) (nat_lit 1048576) (nat_lit 4061117) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 15) (nat_lit 1) (nat_lit 2030558) (nat_lit 2030559) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31928 :=
@p31924 (nat_lit 524288)
  (@p31925 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 15))
    (p31927 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31933 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 51153586820399524478976) (nat_lit 18889465931478580854784)

noncomputable def p31934 :=
BSN.log_rat_reduce_isNear (nat_lit 15) (nat_lit 1) (nat_lit 3) (nat_lit 30) (nat_lit 16) (nat_lit 329571)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31935 :=
BSN.log_dyadic_bound (nat_lit 7) (nat_lit 23) (nat_lit 6) (nat_lit 5) (nat_lit 430628584065881355) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 14087658153505881) (nat_lit 266939110305) (nat_lit 329571) (nat_lit 30)

noncomputable def p31936 :=
p31935 (nat_lit 16) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31937 :=
@BSN.binarySplit_of_base5 (BSN.artanhP (nat_lit 7)) (BSN.artanhQ (nat_lit 23)) (nat_lit 0) (nat_lit 5)
  (nat_lit 14087658153505881) (nat_lit 430628584065881355) (nat_lit 266939110305) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p31938 :=
p31934 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p31936 (p31937 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p31978 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16)))) false
  (nat_lit 262143) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p31979 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16))) (nat_lit 4194305)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 131071) (nat_lit 131072)

noncomputable def p31980 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4194305) (nat_lit 1048576)

noncomputable def p31981 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4194305) (nat_lit 1048576)

noncomputable def p31982 :=
@p31981 (nat_lit 1) (nat_lit 1048576) (nat_lit 4194305) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 16) (nat_lit 1) (nat_lit 2097152) (nat_lit 2097153) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p31983 :=
@p31979 (nat_lit 524288)
  (@p31980 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 16))
    (p31982 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p31988 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 52372720210750067441664) (nat_lit 18889465931478580854784)

noncomputable def p31989 :=
BSN.log_rat_reduce_isNear (nat_lit 16) (nat_lit 1) (nat_lit 4) (nat_lit 32) (nat_lit 32) (nat_lit 0) (nat_lit 524288)
  (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p31990 :=
BSN.log_dyadic_bound (nat_lit 0) (nat_lit 32) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 524288) (nat_lit 200000)
  (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 32)

noncomputable def p31991 :=
p31990 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31992 :=
p31991
  (@BSN.binarySplit_of_le (BSN.artanhP (nat_lit 0)) (BSN.artanhQ (nat_lit 32)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p31993 :=
p31989 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) p31992 BSN.log2_near_15 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32073 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17)))) false
  (nat_lit 254317) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32074 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17))) (nat_lit 4323389)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 127158) (nat_lit 127159)

noncomputable def p32075 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4323389) (nat_lit 1048576)

noncomputable def p32076 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4323389) (nat_lit 1048576)

noncomputable def p32077 :=
@p32076 (nat_lit 1) (nat_lit 1048576) (nat_lit 4323389) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 17) (nat_lit 1) (nat_lit 2161694) (nat_lit 2161695) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32078 :=
@p32074 (nat_lit 524288)
  (@p32075 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 17))
    (p32077 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32083 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 53517859495200818200576) (nat_lit 18889465931478580854784)

noncomputable def p32084 :=
BSN.log_rat_reduce_isNear (nat_lit 17) (nat_lit 1) (nat_lit 4) (nat_lit 34) (nat_lit 32) (nat_lit 31784)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32085 :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 33) (nat_lit 2) (nat_lit 1) (nat_lit 3267) (nat_lit 524288) (nat_lit 200000)
  (nat_lit 1) (nat_lit 1) (nat_lit 31784) (nat_lit 34)

noncomputable def p32086 :=
p32085 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32087 :=
@BSN.binarySplit_of_base (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 33)) (nat_lit 0) (nat_lit 1) (nat_lit 1)
  (nat_lit 3267) (nat_lit 1) (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32088 :=
p32084 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32086 (p32087 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32127 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18)))) false
  (nat_lit 247151) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32128 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18))) (nat_lit 4448731)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 123575) (nat_lit 123576)

noncomputable def p32129 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4448731) (nat_lit 1048576)

noncomputable def p32130 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4448731) (nat_lit 1048576)

noncomputable def p32131 :=
@p32130 (nat_lit 1) (nat_lit 1048576) (nat_lit 4448731) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 18) (nat_lit 1) (nat_lit 2224365) (nat_lit 2224366) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32132 :=
@p32128 (nat_lit 524288)
  (@p32129 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 18))
    (p32131 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32137 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 54597570484265130393600) (nat_lit 18889465931478580854784)

noncomputable def p32138 :=
BSN.log_rat_reduce_isNear (nat_lit 18) (nat_lit 1) (nat_lit 4) (nat_lit 36) (nat_lit 32) (nat_lit 61752)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32139 :=
BSN.log_dyadic_bound (nat_lit 2) (nat_lit 34) (nat_lit 3) (nat_lit 2) (nat_lit 20045040) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 23168) (nat_lit 48) (nat_lit 61752) (nat_lit 36)

noncomputable def p32140 :=
p32139 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32141 :=
@BSN.binarySplit_of_base2 (BSN.artanhP (nat_lit 2)) (BSN.artanhQ (nat_lit 34)) (nat_lit 0) (nat_lit 2) (nat_lit 23168)
  (nat_lit 20045040) (nat_lit 48) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32142 :=
p32138 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32140 (p32141 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32182 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19)))) false
  (nat_lit 240559) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32183 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19))) (nat_lit 4570637)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 120279) (nat_lit 120280)

noncomputable def p32184 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4570637) (nat_lit 1048576)

noncomputable def p32185 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4570637) (nat_lit 1048576)

noncomputable def p32186 :=
@p32185 (nat_lit 1) (nat_lit 1048576) (nat_lit 4570637) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 19) (nat_lit 1) (nat_lit 2285318) (nat_lit 2285319) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32187 :=
@p32183 (nat_lit 524288)
  (@p32184 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 19))
    (p32186 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32192 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 55618878793361701994496) (nat_lit 18889465931478580854784)

noncomputable def p32193 :=
BSN.log_rat_reduce_isNear (nat_lit 19) (nat_lit 1) (nat_lit 4) (nat_lit 38) (nat_lit 32) (nat_lit 90099)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32194 :=
BSN.log_dyadic_bound (nat_lit 3) (nat_lit 35) (nat_lit 3) (nat_lit 2) (nat_lit 22509375) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 55368) (nat_lit 243) (nat_lit 90099) (nat_lit 38)

noncomputable def p32195 :=
p32194 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32196 :=
@BSN.binarySplit_of_base2 (BSN.artanhP (nat_lit 3)) (BSN.artanhQ (nat_lit 35)) (nat_lit 0) (nat_lit 2) (nat_lit 55368)
  (nat_lit 22509375) (nat_lit 243) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32197 :=
p32193 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32195 (p32196 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32237 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20)))) false
  (nat_lit 234469) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32238 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20))) (nat_lit 4689375)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 117234) (nat_lit 117235)

noncomputable def p32239 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4689375) (nat_lit 1048576)

noncomputable def p32240 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4689375) (nat_lit 1048576)

noncomputable def p32241 :=
@p32240 (nat_lit 1) (nat_lit 1048576) (nat_lit 4689375) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 20) (nat_lit 1) (nat_lit 2344687) (nat_lit 2344688) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32242 :=
@p32238 (nat_lit 524288)
  (@p32239 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 20))
    (p32241 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32247 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 56587765202795681021952) (nat_lit 18889465931478580854784)

noncomputable def p32248 :=
BSN.log_rat_reduce_isNear (nat_lit 20) (nat_lit 1) (nat_lit 4) (nat_lit 40) (nat_lit 32) (nat_lit 116991)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32249 :=
BSN.log_dyadic_bound (nat_lit 4) (nat_lit 36) (nat_lit 3) (nat_lit 2) (nat_lit 25194240) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 104448) (nat_lit 768) (nat_lit 116991) (nat_lit 40)

noncomputable def p32250 :=
p32249 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32251 :=
@BSN.binarySplit_of_base2 (BSN.artanhP (nat_lit 4)) (BSN.artanhQ (nat_lit 36)) (nat_lit 0) (nat_lit 2) (nat_lit 104448)
  (nat_lit 25194240) (nat_lit 768) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32252 :=
p32248 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32250 (p32251 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32292 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21)))) false
  (nat_lit 228818) (nat_lit 1048576) (nat_lit 2) (nat_lit 1048576)

noncomputable def p32293 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21))) (nat_lit 4805179)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 114408) (nat_lit 114410)

noncomputable def p32294 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4805179) (nat_lit 1048576)

noncomputable def p32295 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4805179) (nat_lit 1048576)

noncomputable def p32296 :=
@p32295 (nat_lit 1) (nat_lit 1048576) (nat_lit 4805179) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 21) (nat_lit 1) (nat_lit 2402589) (nat_lit 2402590) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32297 :=
@p32293 (nat_lit 524288)
  (@p32294 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 21))
    (p32296 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32302 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 57509381830540779323392) (nat_lit 18889465931478580854784)

noncomputable def p32303 :=
BSN.log_rat_reduce_isNear (nat_lit 21) (nat_lit 1) (nat_lit 4) (nat_lit 42) (nat_lit 32) (nat_lit 142571)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32304 :=
BSN.log_dyadic_bound (nat_lit 5) (nat_lit 37) (nat_lit 4) (nat_lit 3) (nat_lit 269401272945) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 1658093375) (nat_lit 234375) (nat_lit 142571) (nat_lit 42)

noncomputable def p32305 :=
p32304 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32306 :=
@BSN.binarySplit_of_base3 (BSN.artanhP (nat_lit 5)) (BSN.artanhQ (nat_lit 37)) (nat_lit 0) (nat_lit 3)
  (nat_lit 1658093375) (nat_lit 269401272945) (nat_lit 234375) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32307 :=
p32303 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32305 (p32306 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32347 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22)))) false
  (nat_lit 223557) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32348 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22))) (nat_lit 4918257)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 111778) (nat_lit 111779)

noncomputable def p32349 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4918257) (nat_lit 1048576)

noncomputable def p32350 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 4918257) (nat_lit 1048576)

noncomputable def p32351 :=
@p32350 (nat_lit 1) (nat_lit 1048576) (nat_lit 4918257) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 22) (nat_lit 1) (nat_lit 2459128) (nat_lit 2459129) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32352 :=
@p32348 (nat_lit 524288)
  (@p32349 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 22))
    (p32351 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32357 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 58388124189833310502912) (nat_lit 18889465931478580854784)

noncomputable def p32358 :=
BSN.log_rat_reduce_isNear (nat_lit 22) (nat_lit 1) (nat_lit 4) (nat_lit 44) (nat_lit 32) (nat_lit 166961)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32359 :=
BSN.log_dyadic_bound (nat_lit 6) (nat_lit 38) (nat_lit 4) (nat_lit 3) (nat_lit 316148320320) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 2667271104) (nat_lit 699840) (nat_lit 166961) (nat_lit 44)

noncomputable def p32360 :=
p32359 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32361 :=
@BSN.binarySplit_of_base3 (BSN.artanhP (nat_lit 6)) (BSN.artanhQ (nat_lit 38)) (nat_lit 0) (nat_lit 3)
  (nat_lit 2667271104) (nat_lit 316148320320) (nat_lit 699840) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32362 :=
p32358 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32360 (p32361 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32402 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23)))) false
  (nat_lit 218643) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32403 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23))) (nat_lit 5028793)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 109321) (nat_lit 109322)

noncomputable def p32404 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5028793) (nat_lit 1048576)

noncomputable def p32405 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5028793) (nat_lit 1048576)

noncomputable def p32406 :=
@p32405 (nat_lit 1) (nat_lit 1048576) (nat_lit 5028793) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 23) (nat_lit 1) (nat_lit 2514396) (nat_lit 2514397) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32407 :=
@p32403 (nat_lit 524288)
  (@p32404 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 23))
    (p32406 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32412 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 59227775304360265777152) (nat_lit 18889465931478580854784)

noncomputable def p32413 :=
BSN.log_rat_reduce_isNear (nat_lit 23) (nat_lit 1) (nat_lit 4) (nat_lit 46) (nat_lit 32) (nat_lit 190266)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32414 :=
BSN.log_dyadic_bound (nat_lit 7) (nat_lit 39) (nat_lit 4) (nat_lit 3) (nat_lit 369468094905) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 4046006391) (nat_lit 1764735) (nat_lit 190266) (nat_lit 46)

noncomputable def p32415 :=
p32414 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32416 :=
@BSN.binarySplit_of_base3 (BSN.artanhP (nat_lit 7)) (BSN.artanhQ (nat_lit 39)) (nat_lit 0) (nat_lit 3)
  (nat_lit 4046006391) (nat_lit 369468094905) (nat_lit 1764735) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32417 :=
p32413 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32415 (p32416 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32457 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24)))) false
  (nat_lit 214039) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32458 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24))) (nat_lit 5136953)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 107019) (nat_lit 107020)

noncomputable def p32459 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5136953) (nat_lit 1048576)

noncomputable def p32460 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5136953) (nat_lit 1048576)

noncomputable def p32461 :=
@p32460 (nat_lit 1) (nat_lit 1048576) (nat_lit 5136953) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 24) (nat_lit 1) (nat_lit 2568476) (nat_lit 2568477) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32462 :=
@p32458 (nat_lit 524288)
  (@p32459 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 24))
    (p32461 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32467 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 60031721881041427759104) (nat_lit 18889465931478580854784)

noncomputable def p32468 :=
BSN.log_rat_reduce_isNear (nat_lit 24) (nat_lit 1) (nat_lit 4) (nat_lit 48) (nat_lit 32) (nat_lit 212580)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32469 :=
BSN.log_dyadic_bound (nat_lit 8) (nat_lit 40) (nat_lit 4) (nat_lit 3) (nat_lit 430080000000) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 5875957760) (nat_lit 3932160) (nat_lit 212580) (nat_lit 48)

noncomputable def p32470 :=
p32469 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32471 :=
@BSN.binarySplit_of_base3 (BSN.artanhP (nat_lit 8)) (BSN.artanhQ (nat_lit 40)) (nat_lit 0) (nat_lit 3)
  (nat_lit 5875957760) (nat_lit 430080000000) (nat_lit 3932160) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32472 :=
p32468 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32470 (p32471 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p129093 :=
BSN.headSumC
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex
      (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
      (@OfNat.ofNat.{0} Complex (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
    (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
      ↑(Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))))

noncomputable def p129094 :=
Enclosure.Complex.IsNear (p129093 (nat_lit 9)) false (nat_lit 412813913099)
  (nat_lit 1099511627776) (nat_lit 2907006304033) (nat_lit 3435973836800000) true (nat_lit 25432974189)
  (nat_lit 137438953472) (nat_lit 362860086051)

noncomputable def p129095 :=
@Neg.neg.{0} Complex Complex.instNeg
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex
      (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
      (@OfNat.ofNat.{0} Complex (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
    (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
      ↑(Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))))

noncomputable def p129096 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 9))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 8))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 8)) p129095))
  false (nat_lit 412813913099) (nat_lit 1099511627776)

noncomputable def p129097 :=
BSN.head_sum_c_succ
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex
      (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
      (@OfNat.ofNat.{0} Complex (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
    (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
      ↑(Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))))

noncomputable def p129098 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 8))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 8)) p129095)
  false (nat_lit 65617632031) (nat_lit 549755813888) (nat_lit 1300988181053)

noncomputable def p129099 :=
@p129098 (nat_lit 1717986918400000) false (nat_lit 32272196845) (nat_lit 549755813888)
  (nat_lit 1298982568553) (nat_lit 1717986918400000) false (nat_lit 281578649037) (nat_lit 1099511627776)
  (nat_lit 305029941927) (nat_lit 3435973836800000)

noncomputable def p129100 :=
@p129099 true (nat_lit 134004093601) (nat_lit 549755813888) (nat_lit 152457775651)
  (nat_lit 1717986918400000) false (nat_lit 226946848780030849318912) (nat_lit 412813913099)
  (nat_lit 1099511627776) (nat_lit 2907006304033) (nat_lit 3435973836800000)

noncomputable def p129101 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 8))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 7))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 7)) p129095))
  false (nat_lit 65617632031) (nat_lit 549755813888)

noncomputable def p129102 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 7))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 7)) p129095)
  true (nat_lit 225342698013) (nat_lit 1099511627776) (nat_lit 2274372041297)

noncomputable def p129103 :=
@p129102 (nat_lit 3435973836800000) false (nat_lit 138991422245) (nat_lit 549755813888)
  (nat_lit 567872365793) (nat_lit 858993459200000) false (nat_lit 356577962075) (nat_lit 1099511627776)
  (nat_lit 327604320809) (nat_lit 3435973836800000)

noncomputable def p129104 :=
@p129103 true (nat_lit 13339903175) (nat_lit 68719476736) (nat_lit 163237836967)
  (nat_lit 1717986918400000) false (nat_lit 144294698810422813786112) (nat_lit 65617632031) (nat_lit 549755813888)
  (nat_lit 1300988181053) (nat_lit 1717986918400000)

noncomputable def p129105 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 7))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 6))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 6)) p129095))
  true (nat_lit 225342698013) (nat_lit 1099511627776)

noncomputable def p129106 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 6))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 6)) p129095)
  true (nat_lit 286302545841) (nat_lit 549755813888) (nat_lit 961179672101)

noncomputable def p129107 :=
@p129106 (nat_lit 1717986918400000) true (nat_lit 6439264295) (nat_lit 1099511627776)
  (nat_lit 1919935503577) (nat_lit 3435973836800000) false (nat_lit 347262393669) (nat_lit 1099511627776)
  (nat_lit 70402539419) (nat_lit 687194767360000)

noncomputable def p129108 :=
@p129107 false (nat_lit 284422108785) (nat_lit 1099511627776) (nat_lit 70310791919)
  (nat_lit 687194767360000) true (nat_lit 123883458349854615404544) (nat_lit 225342698013) (nat_lit 1099511627776)
  (nat_lit 2274372041297) (nat_lit 3435973836800000)

noncomputable def p129109 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 6))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 5))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 5)) p129095))
  true (nat_lit 286302545841) (nat_lit 549755813888)

noncomputable def p129110 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 5))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 5)) p129095)
  true (nat_lit 85878966587) (nat_lit 1099511627776) (nat_lit 306963377177)

noncomputable def p129111 :=
@p129110 (nat_lit 687194767360000) false (nat_lit 63431410831) (nat_lit 1099511627776)
  (nat_lit 307034194677) (nat_lit 687194767360000) true (nat_lit 486726125095) (nat_lit 1099511627776)
  (nat_lit 387542458317) (nat_lit 3435973836800000)

noncomputable def p129112 :=
@p129111 true (nat_lit 34935337563) (nat_lit 549755813888) (nat_lit 24047783137)
  (nat_lit 214748364800000) true (nat_lit 629585956428101537759232) (nat_lit 286302545841) (nat_lit 549755813888)
  (nat_lit 961179672101) (nat_lit 1717986918400000)

noncomputable def p129113 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 5))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 4))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 4)) p129095))
  true (nat_lit 85878966587) (nat_lit 1099511627776)

noncomputable def p129114 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 4))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 4)) p129095)
  true (nat_lit 76806704339) (nat_lit 1099511627776) (nat_lit 1105104076293)

noncomputable def p129115 :=
@p129114 (nat_lit 3435973836800000) true (nat_lit 474851935) (nat_lit 1073741824)
  (nat_lit 275558971417) (nat_lit 858993459200000) true (nat_lit 1134032781) (nat_lit 137438953472)
  (nat_lit 53714101199) (nat_lit 429496729600000)

noncomputable def p129116 :=
@p129115 false (nat_lit 549679792271) (nat_lit 1099511627776) (nat_lit 432935087717)
  (nat_lit 3435973836800000) true (nat_lit 11803115292974135640064) (nat_lit 85878966587) (nat_lit 1099511627776)
  (nat_lit 306963377177) (nat_lit 687194767360000)

noncomputable def p129117 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 4))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 3))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 3)) p129095))
  true (nat_lit 76806704339) (nat_lit 1099511627776)

noncomputable def p129118 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 3))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 3)) p129095)
  false (nat_lit 138584390299) (nat_lit 274877906944) (nat_lit 151902638151)

noncomputable def p129119 :=
@p129118 (nat_lit 858993459200000) true (nat_lit 277149205905) (nat_lit 549755813888)
  (nat_lit 303824504427) (nat_lit 1717986918400000) true (nat_lit 631144265535) (nat_lit 1099511627776)
  (nat_lit 497493523689) (nat_lit 3435973836800000)

noncomputable def p129120 :=
@p129119 false (nat_lit 34025015185) (nat_lit 549755813888) (nat_lit 247293438407)
  (nat_lit 1717986918400000) true (nat_lit 21112466127970963030016) (nat_lit 76806704339) (nat_lit 1099511627776)
  (nat_lit 1105104076293) (nat_lit 3435973836800000)

noncomputable def p129121 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 3))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 2))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2)) p129095))
  false (nat_lit 138584390299) (nat_lit 274877906944)

noncomputable def p129122 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 2))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2)) p129095)
  false (nat_lit 1) (nat_lit 1) (nat_lit 0)

noncomputable def p129123 :=
@p129122 (nat_lit 1) false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) true
  (nat_lit 136293516645) (nat_lit 274877906944) (nat_lit 151902638151) (nat_lit 858993459200000)

noncomputable def p129124 :=
@p129123 true (nat_lit 277149205905) (nat_lit 549755813888) (nat_lit 303824504427)
  (nat_lit 1717986918400000) false (nat_lit 138584390299) (nat_lit 138584390299) (nat_lit 274877906944)
  (nat_lit 151902638151) (nat_lit 858993459200000)

noncomputable def p129125 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 2))
  { re := Enclosure.sfrac false (nat_lit 1) (nat_lit 1), im := Enclosure.sfrac false (nat_lit 0) (nat_lit 1) }
  false (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1)

noncomputable def p129126 :=
BSN.head_sum_c_two
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex
      (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
      (@OfNat.ofNat.{0} Complex (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
    (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
      ↑(Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))))

noncomputable def p129127 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1)))))) }

noncomputable def p129128 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 2)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129129 :=
@p129127 true (nat_lit 136293516645) (nat_lit 274877906944) (nat_lit 151902638151)
  (nat_lit 858993459200000) true (nat_lit 277149205905) (nat_lit 549755813888) (nat_lit 303824504427)
  (nat_lit 1717986918400000) p129128

noncomputable def p129130 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1)))))))
  true

noncomputable def p129131 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1)))))
  (nat_lit 741455) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129132 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1)))))
  true (nat_lit 735276) (nat_lit 1048576)

noncomputable def p129133 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17701967)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 17701967) (nat_lit 524288)

noncomputable def p129134 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1))))
  false (nat_lit 1106372943) (nat_lit 32768000) (nat_lit 48711)

noncomputable def p129135 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0) (nat_lit 1)
  (nat_lit 363408) (nat_lit 524288)

noncomputable def p129136 :=
@p129135 (nat_lit 1) (nat_lit 200000) (nat_lit 1106372943) (nat_lit 32768000) (nat_lit 48711)
  (nat_lit 200000000) (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 2) (nat_lit 1) (nat_lit 363408) (nat_lit 524288) (nat_lit 1) (nat_lit 200000)
    false
    (p31213
      (p31215 (p31216 (Eq.refl true)) (Eq.refl true)
        (Eq.refl true) (Eq.refl true) (Eq.refl true))))

noncomputable def p129137 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17701967)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 58715992693747046416384))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129138 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 17701967) (nat_lit 524288) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 5) (nat_lit 58715992693747046416384) (nat_lit 75557863725914323419136)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129139 :=
nat_lit 7755796605962430693174859041885720721

noncomputable def p129140 :=
BSN.sin_dyadic_bound_f (nat_lit 1668808883) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129139 p31525 p129139
  p129139 p31526

noncomputable def p129141 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1668808883)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129139 p31525 p129139 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129142 :=
p129140 p129139 (nat_lit 735276) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129141 (Eq.refl true))

noncomputable def p129143 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1668808883)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129139 p31526 p129139 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129144 :=
@BSN.sin_arg_round false (nat_lit 735276) (nat_lit 1048576) (nat_lit 58715992693747046416384)
  (nat_lit 75557863725914323419136) (nat_lit 1668808883) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129142 (p129143 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129145 :=
p129137 (nat_lit 735276) (nat_lit 1048576) (nat_lit 5) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129138 BSN.pi_near_15 p129144 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129146 :=
@p129133 (nat_lit 1) (nat_lit 4096) true (nat_lit 735276) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129134 (nat_lit 200000000) (nat_lit 17701967) (nat_lit 524288) (nat_lit 1) (nat_lit 4096)
    (p129136 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 17701967) (nat_lit 524288))
  (p129145 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129147 :=
@p129131 (nat_lit 1048576) (nat_lit 183819) (nat_lit 262144) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 136293516645) (nat_lit 274877906944) (nat_lit 151902638151) (nat_lit 858993459200000)
  (@p31204 (nat_lit 741455) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31209
    (Eq.refl true))
  (@p129132 (nat_lit 204096) (nat_lit 819200000) (nat_lit 183819) (nat_lit 262144) (nat_lit 3189)
    (nat_lit 12800000) (p129146 (Eq.refl true)) (Eq.refl true))

noncomputable def p129148 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 2))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1))))))
  (nat_lit 741455) (nat_lit 1048576)

noncomputable def p129149 :=
@p129148 (nat_lit 1) (nat_lit 1048576) (nat_lit 373791) (nat_lit 524288) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 277149205905) (nat_lit 549755813888) (nat_lit 303824504427) (nat_lit 1717986918400000)
  (@p31204 (nat_lit 741455) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31209
    (Eq.refl true))

noncomputable def p129150 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1)))))
  false (nat_lit 373791) (nat_lit 524288)

noncomputable def p129151 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1)))))
  false (nat_lit 747582) (nat_lit 1048576)

noncomputable def p129152 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 2) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17701967)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 17701967) (nat_lit 524288)

noncomputable def p129153 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17701967)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 58715992693747046416384))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129154 :=
nat_lit 277172039156592146783907347513200325157955891404608558728968622864744930636321

noncomputable def p129155 :=
nat_lit 60152380993058359431273009695986690798569260535162171539520278317608759841

noncomputable def p129156 :=
nat_lit 831395812707790323632859496520209002092270535692755351843826828037599574389281

noncomputable def p129157 :=
BSN.cos_dyadic_bound_f (nat_lit 1668808883) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129154 p31681 p129155
  p129156 p31684

noncomputable def p129158 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1668808883)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129154 p31681 p129155 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129159 :=
p129157 p129155 (nat_lit 747582) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129158 (Eq.refl true))

noncomputable def p129160 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1668808883)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129156 p31684 p129155 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129161 :=
@BSN.cos_arg_round false (nat_lit 747582) (nat_lit 1048576) (nat_lit 58715992693747046416384)
  (nat_lit 75557863725914323419136) (nat_lit 1668808883) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129159 (p129160 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129162 :=
p129153 (nat_lit 747582) (nat_lit 1048576) (nat_lit 5) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129138 BSN.pi_near_15 p129161 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129163 :=
@p129152 (nat_lit 1) (nat_lit 4096) false (nat_lit 747582) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129134 (nat_lit 200000000) (nat_lit 17701967) (nat_lit 524288) (nat_lit 1) (nat_lit 4096)
    (p129136 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 17701967) (nat_lit 524288))
  (p129162 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129164 :=
p129149
  (@p129150 (nat_lit 3189) (nat_lit 12800000)
    (@p129151 (nat_lit 204096) (nat_lit 819200000) (nat_lit 373791) (nat_lit 524288) (nat_lit 3189)
      (nat_lit 12800000) (p129163 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129165 :=
@p129130 (nat_lit 136293516645) (nat_lit 274877906944) (nat_lit 151902638151)
  (nat_lit 858993459200000) true (nat_lit 277149205905) (nat_lit 549755813888) (nat_lit 303824504427)
  (nat_lit 1717986918400000) (p129147 (Eq.refl true)) p129164

noncomputable def p129166 :=
@p129124 true (nat_lit 277149205905) (nat_lit 277149205905) (nat_lit 549755813888)
  (nat_lit 303824504427) (nat_lit 1717986918400000)
  (@p129125 false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) p129126
    (@p31198 (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1)
      (Enclosure.Real.IsNear.const false (nat_lit 1) (nat_lit 1))
      (Enclosure.Real.IsNear.const false (nat_lit 0) (nat_lit 1))))
  (p129129 p129165) (Eq.refl true) (Eq.refl true)

noncomputable def p129167 :=
p129166 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129168 :=
@p129120 true (nat_lit 133658937345134936719360) (nat_lit 474851935) (nat_lit 1073741824)
  (nat_lit 275558971417) (nat_lit 858993459200000)
  (@p129121 (nat_lit 151902638151) (nat_lit 858993459200000) true (nat_lit 277149205905)
    (nat_lit 549755813888) (nat_lit 303824504427) (nat_lit 1717986918400000)
    (p129097 (nat_lit 2) (nat_lit 3) (Eq.refl true) (Eq.refl true))
    (p129167 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))

noncomputable def p129169 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 3)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1)))))) }

noncomputable def p129170 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 3)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129171 :=
@p129169 true (nat_lit 631144265535) (nat_lit 1099511627776) (nat_lit 497493523689)
  (nat_lit 3435973836800000) false (nat_lit 34025015185) (nat_lit 549755813888) (nat_lit 247293438407)
  (nat_lit 1717986918400000) p129170

noncomputable def p129172 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1)))))))
  true

noncomputable def p129173 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1)))))
  (nat_lit 605395) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129174 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1)))))
  true (nat_lit 1042533) (nat_lit 1048576)

noncomputable def p129175 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3507125)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  false (nat_lit 3507125) (nat_lit 65536)

noncomputable def p129176 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1))))
  false (nat_lit 28057000179) (nat_lit 524288000) (nat_lit 48711)

noncomputable def p129177 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0) (nat_lit 1)
  (nat_lit 575989) (nat_lit 524288)

noncomputable def p129178 :=
@p129177 (nat_lit 1) (nat_lit 200000) (nat_lit 28057000179) (nat_lit 524288000) (nat_lit 48711)
  (nat_lit 200000000) (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 3) (nat_lit 1) (nat_lit 575989) (nat_lit 524288) (nat_lit 1) (nat_lit 200000)
    false
    (p31258
      (p31260 (p31261 (Eq.refl true)) (Eq.refl true)
        (Eq.refl true) (Eq.refl true) (Eq.refl true))))

noncomputable def p129179 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3507125)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1014416075709826990080))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9444732965739290427392)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129180 :=
BSN.sin_reduce_arg_pos_rat_q2 (nat_lit 3507125) (nat_lit 65536) (nat_lit 226375608064910080) (nat_lit 72057594037927936)
  (nat_lit 8) (nat_lit 1014416075709826990080) (nat_lit 9444732965739290427392) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129181 :=
nat_lit 2830252717642730678472581322100641

noncomputable def p129182 :=
BSN.cos_dyadic_bound_f (nat_lit 230651511) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129181 p31541 p129181
  p129181 p31542

noncomputable def p129183 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 230651511)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129181 p31541 p129181 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129184 :=
p129182 p129181 (nat_lit 1042533) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129183 (Eq.refl true))

noncomputable def p129185 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 230651511)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129181 p31542 p129181 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129186 :=
@BSN.cos_arg_round false (nat_lit 1042533) (nat_lit 1048576) (nat_lit 1014416075709826990080)
  (nat_lit 9444732965739290427392) (nat_lit 230651511) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129184 (p129185 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129187 :=
p129179 (nat_lit 1042533) (nat_lit 1048576) (nat_lit 8) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129180 BSN.pi_near_15 p129186 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129188 :=
@p129175 (nat_lit 1) (nat_lit 4096) true (nat_lit 1042533) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129176 (nat_lit 200000000) (nat_lit 3507125) (nat_lit 65536) (nat_lit 1) (nat_lit 4096)
    (p129178 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 3507125) (nat_lit 65536))
  (p129187 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129189 :=
@p129173 (nat_lit 1048576) (nat_lit 1042533) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 631144265535) (nat_lit 1099511627776) (nat_lit 497493523689) (nat_lit 3435973836800000)
  (@p31249 (nat_lit 605395) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31254
    (Eq.refl true))
  (@p129174 (nat_lit 204096) (nat_lit 819200000) (nat_lit 1042533) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p129188 (Eq.refl true)) (Eq.refl true))

noncomputable def p129190 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1))))))
  (nat_lit 605395) (nat_lit 1048576)

noncomputable def p129191 :=
@p129190 (nat_lit 1) (nat_lit 1048576) (nat_lit 56203) (nat_lit 524288) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 34025015185) (nat_lit 549755813888) (nat_lit 247293438407) (nat_lit 1717986918400000)
  (@p31249 (nat_lit 605395) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31254
    (Eq.refl true))

noncomputable def p129192 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1)))))
  true (nat_lit 56203) (nat_lit 524288)

noncomputable def p129193 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1)))))
  true (nat_lit 112406) (nat_lit 1048576)

noncomputable def p129194 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 3) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3507125)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  false (nat_lit 3507125) (nat_lit 65536)

noncomputable def p129195 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3507125)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1014416075709826990080))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9444732965739290427392)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129196 :=
BSN.sin_dyadic_bound_f (nat_lit 230651511) (nat_lit 2147483648) (nat_lit 1) (nat_lit 0) (nat_lit 1048576)
  (nat_lit 400391) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1)

noncomputable def p129197 :=
p129196 (nat_lit 1) (nat_lit 112406) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.sinEvenP (nat_lit 230651511)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))

noncomputable def p129198 :=
p129197
  (@BSN.binarySplit_of_le (BSN.sinOddP (nat_lit 230651511)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129199 :=
@BSN.sin_arg_round false (nat_lit 112406) (nat_lit 1048576) (nat_lit 1014416075709826990080)
  (nat_lit 9444732965739290427392) (nat_lit 230651511) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  p129198 (Eq.refl true)

noncomputable def p129200 :=
p129195 (nat_lit 112406) (nat_lit 1048576) (nat_lit 8) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129180 BSN.pi_near_15 p129199 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129201 :=
@p129194 (nat_lit 1) (nat_lit 4096) true (nat_lit 112406) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129176 (nat_lit 200000000) (nat_lit 3507125) (nat_lit 65536) (nat_lit 1) (nat_lit 4096)
    (p129178 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 3507125) (nat_lit 65536))
  (p129200 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129202 :=
p129191
  (@p129192 (nat_lit 3189) (nat_lit 12800000)
    (@p129193 (nat_lit 204096) (nat_lit 819200000) (nat_lit 56203) (nat_lit 524288) (nat_lit 3189)
      (nat_lit 12800000) (p129201 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129203 :=
@p129172 (nat_lit 631144265535) (nat_lit 1099511627776) (nat_lit 497493523689)
  (nat_lit 3435973836800000) false (nat_lit 34025015185) (nat_lit 549755813888) (nat_lit 247293438407)
  (nat_lit 1717986918400000) (p129189 (Eq.refl true)) p129202

noncomputable def p129204 :=
p129168 (p129171 p129203) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129205 :=
p129204 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129206 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 4)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1)))))) }

noncomputable def p129207 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 4)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129208 :=
@p129206 true (nat_lit 1134032781) (nat_lit 137438953472) (nat_lit 53714101199)
  (nat_lit 429496729600000) false (nat_lit 549679792271) (nat_lit 1099511627776) (nat_lit 432935087717)
  (nat_lit 3435973836800000) p129207

noncomputable def p129209 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1)))))))
  true

noncomputable def p129210 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1)))))
  (nat_lit 524287) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129211 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1)))))
  true (nat_lit 17304) (nat_lit 1048576)

noncomputable def p129212 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 70807965)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 70807965) (nat_lit 1048576)

noncomputable def p129213 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1))))
  false (nat_lit 35403982887) (nat_lit 524288000) (nat_lit 48711)

noncomputable def p129214 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0) (nat_lit 1)
  (nat_lit 726817) (nat_lit 524288)

noncomputable def p129215 :=
@p129214 (nat_lit 1) (nat_lit 200000) (nat_lit 35403982887) (nat_lit 524288000) (nat_lit 48711)
  (nat_lit 200000000) (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 4) (nat_lit 1) (nat_lit 726817) (nat_lit 524288) (nat_lit 1) (nat_lit 200000)
    false
    (p31306
      (p31311 (p31312 (Eq.refl true)) (Eq.refl true)
        (Eq.refl true) (Eq.refl true) (Eq.refl true))))

noncomputable def p129216 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 70807965)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 234877949948231543685120))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129217 :=
BSN.sin_reduce_arg_pos_rat_q2 (nat_lit 70807965) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 10) (nat_lit 234877949948231543685120) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129218 :=
nat_lit 4450252228180444495677705165095275696068838134527875940241098454620706775900416

noncomputable def p129219 :=
nat_lit 15406343490845849844962965689082272441982923721999495292013173994506725499136

noncomputable def p129220 :=
nat_lit 13319943997559641787343189563907662543322548556139628830139269015873106876702976

noncomputable def p129221 :=
BSN.cos_dyadic_bound_f (nat_lit 3337816422) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129218 p31681 p129219
  p129220 p31684

noncomputable def p129222 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 3337816422)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129218 p31681 p129219 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129223 :=
p129221 p129219 (nat_lit 17304) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129222 (Eq.refl true))

noncomputable def p129224 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 3337816422)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129220 p31684 p129219 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129225 :=
@BSN.cos_arg_round false (nat_lit 17304) (nat_lit 1048576) (nat_lit 234877949948231543685120)
  (nat_lit 151115727451828646838272) (nat_lit 3337816422) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129223 (p129224 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129226 :=
p129216 (nat_lit 17304) (nat_lit 1048576) (nat_lit 10) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129217 BSN.pi_near_15 p129225 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129227 :=
@p129212 (nat_lit 257) (nat_lit 1048576) true (nat_lit 17304) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129213 (nat_lit 200000000) (nat_lit 70807965) (nat_lit 1048576) (nat_lit 257) (nat_lit 1048576)
    (p129215 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 70807965) (nat_lit 1048576))
  (p129226 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129228 :=
@p129210 (nat_lit 1048576) (nat_lit 2163) (nat_lit 131072) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 1134032781) (nat_lit 137438953472) (nat_lit 53714101199) (nat_lit 429496729600000)
  (@p31297 (nat_lit 524287) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31302
    (Eq.refl true))
  (@p129211 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 2163) (nat_lit 131072) (nat_lit 819509)
    (nat_lit 3276800000) (p129227 (Eq.refl true)) (Eq.refl true))

noncomputable def p129229 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1))))))
  (nat_lit 524287) (nat_lit 1048576)

noncomputable def p129230 :=
@p129229 (nat_lit 1) (nat_lit 1048576) (nat_lit 1048433) (nat_lit 1048576) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 549679792271) (nat_lit 1099511627776) (nat_lit 432935087717) (nat_lit 3435973836800000)
  (@p31297 (nat_lit 524287) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31302
    (Eq.refl true))

noncomputable def p129231 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1)))))
  true (nat_lit 1048433) (nat_lit 1048576)

noncomputable def p129232 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1)))))
  true (nat_lit 1048433) (nat_lit 1048576)

noncomputable def p129233 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 4) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 70807965)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 70807965) (nat_lit 1048576)

noncomputable def p129234 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 70807965)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 234877949948231543685120))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129235 :=
nat_lit 7998128935932123412343898924620230434970322303172577096200366679121666816221440

noncomputable def p129236 :=
nat_lit 20922536942741810894485033334318279840968586060378274164337700925518021248819456

noncomputable def p129237 :=
BSN.sin_dyadic_bound_f (nat_lit 3337816422) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129235 p31776 p129219
  p129236 p31779

noncomputable def p129238 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 3337816422)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129235 p31776 p129219 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129239 :=
p129237 p129219 (nat_lit 1048433) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129238 (Eq.refl true))

noncomputable def p129240 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 3337816422)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129236 p31779 p129219 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129241 :=
@BSN.sin_arg_round false (nat_lit 1048433) (nat_lit 1048576) (nat_lit 234877949948231543685120)
  (nat_lit 151115727451828646838272) (nat_lit 3337816422) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129239 (p129240 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129242 :=
p129234 (nat_lit 1048433) (nat_lit 1048576) (nat_lit 10) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129217 BSN.pi_near_15 p129241 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129243 :=
@p129233 (nat_lit 257) (nat_lit 1048576) true (nat_lit 1048433) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129213 (nat_lit 200000000) (nat_lit 70807965) (nat_lit 1048576) (nat_lit 257) (nat_lit 1048576)
    (p129215 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 70807965) (nat_lit 1048576))
  (p129242 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129244 :=
p129230
  (@p129231 (nat_lit 819509) (nat_lit 3276800000)
    (@p129232 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 1048433) (nat_lit 1048576)
      (nat_lit 819509) (nat_lit 3276800000) (p129243 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129245 :=
@p129209 (nat_lit 1134032781) (nat_lit 137438953472) (nat_lit 53714101199) (nat_lit 429496729600000)
  false (nat_lit 549679792271) (nat_lit 1099511627776) (nat_lit 432935087717) (nat_lit 3435973836800000)
  (p129228 (Eq.refl true)) p129244

noncomputable def p129246 :=
@p129116 false (nat_lit 68108958764571295744) (nat_lit 63431410831) (nat_lit 1099511627776)
  (nat_lit 307034194677) (nat_lit 687194767360000)
  (@p129117 (nat_lit 1105104076293) (nat_lit 3435973836800000) true (nat_lit 474851935)
    (nat_lit 1073741824) (nat_lit 275558971417) (nat_lit 858993459200000)
    (p129097 (nat_lit 3) (nat_lit 4) (Eq.refl true) (Eq.refl true))
    p129205)
  (p129208 p129245)

noncomputable def p129247 :=
p129246 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129248 :=
p129247 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129249 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 5)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1)))))) }

noncomputable def p129250 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 5)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129251 :=
@p129249 true (nat_lit 486726125095) (nat_lit 1099511627776) (nat_lit 387542458317)
  (nat_lit 3435973836800000) true (nat_lit 34935337563) (nat_lit 549755813888) (nat_lit 24047783137)
  (nat_lit 214748364800000) p129250

noncomputable def p129252 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1)))))))
  true

noncomputable def p129253 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1)))))
  (nat_lit 468937) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129254 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1)))))
  true (nat_lit 1037935) (nat_lit 1048576)

noncomputable def p129255 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41102731)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 41102731) (nat_lit 524288)

noncomputable def p129256 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1))))
  false (nat_lit 1284460359) (nat_lit 16384000) (nat_lit 48711)

noncomputable def p129257 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0) (nat_lit 1)
  (nat_lit 843808) (nat_lit 524288)

noncomputable def p129258 :=
@p129256 (nat_lit 200000000) (nat_lit 41102731) (nat_lit 524288) (nat_lit 257) (nat_lit 1048576)
  (@p129257 (nat_lit 1) (nat_lit 200000) (nat_lit 1284460359) (nat_lit 16384000) (nat_lit 48711)
    (nat_lit 200000000) (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
    (BSN.isNear_log_sfrac (nat_lit 5) (nat_lit 1) (nat_lit 843808) (nat_lit 524288) (nat_lit 1) (nat_lit 200000)
      false
      (p31354
        (p31359 p31363 (Eq.refl true) (Eq.refl true)
          (Eq.refl true) (Eq.refl true))))
    (Eq.refl true))

noncomputable def p129259 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41102731)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 107913083240668276457472))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129260 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 41102731) (nat_lit 524288) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 12) (nat_lit 107913083240668276457472) (nat_lit 75557863725914323419136)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129261 :=
nat_lit 5698959642509919079601867115729922730431364738923802416716765312566625994530625

noncomputable def p129262 :=
nat_lit 7830587911812985020052925593104250454210434945283639027667221208942937890625

noncomputable def p129263 :=
nat_lit 14913168588049709899400994852141914555156281231079499485356257460479065229090625

noncomputable def p129264 :=
BSN.sin_dyadic_bound_f (nat_lit 3067074295) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129261 p31776 p129262
  p129263 p31779

noncomputable def p129265 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 3067074295)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129261 p31776 p129262 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129266 :=
p129264 p129262 (nat_lit 1037935) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129265 (Eq.refl true))

noncomputable def p129267 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 3067074295)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129263 p31779 p129262 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129268 :=
@BSN.sin_arg_round false (nat_lit 1037935) (nat_lit 1048576) (nat_lit 107913083240668276457472)
  (nat_lit 75557863725914323419136) (nat_lit 3067074295) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129266 (p129267 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129269 :=
p129259 (nat_lit 1037935) (nat_lit 1048576) (nat_lit 12) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129260 BSN.pi_near_15 p129268 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129270 :=
@p129255 (nat_lit 257) (nat_lit 1048576) true (nat_lit 1037935) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000) (p129258 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 41102731) (nat_lit 524288))
  (p129269 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129271 :=
@p129253 (nat_lit 1048576) (nat_lit 1037935) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 486726125095) (nat_lit 1099511627776) (nat_lit 387542458317) (nat_lit 3435973836800000)
  (@p31345 (nat_lit 468937) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31350
    (Eq.refl true))
  (@p129254 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 1037935) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p129270 (Eq.refl true))
    (Eq.refl true))

noncomputable def p129272 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1))))))
  (nat_lit 468937) (nat_lit 1048576)

noncomputable def p129273 :=
@p129272 (nat_lit 1) (nat_lit 1048576) (nat_lit 74499) (nat_lit 524288) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 34935337563) (nat_lit 549755813888) (nat_lit 24047783137) (nat_lit 214748364800000)
  (@p31345 (nat_lit 468937) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31350
    (Eq.refl true))

noncomputable def p129274 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1)))))
  false (nat_lit 74499) (nat_lit 524288)

noncomputable def p129275 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1)))))
  false (nat_lit 148998) (nat_lit 1048576)

noncomputable def p129276 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 5) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41102731)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 41102731) (nat_lit 524288)

noncomputable def p129277 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41102731)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 107913083240668276457472))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129278 :=
nat_lit 3169568951577427482009949697891336739330407270488905182188277271963211302690625

noncomputable def p129279 :=
nat_lit 9493045678908656475989743242487801717082800941576148268509497373471748032290625

noncomputable def p129280 :=
BSN.cos_dyadic_bound_f (nat_lit 3067074295) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129278 p31681 p129262
  p129279 p31684

noncomputable def p129281 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 3067074295)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129278 p31681 p129262 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129282 :=
p129280 p129262 (nat_lit 148998) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129281 (Eq.refl true))

noncomputable def p129283 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 3067074295)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129279 p31684 p129262 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129284 :=
@BSN.cos_arg_round false (nat_lit 148998) (nat_lit 1048576) (nat_lit 107913083240668276457472)
  (nat_lit 75557863725914323419136) (nat_lit 3067074295) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129282 (p129283 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129285 :=
p129277 (nat_lit 148998) (nat_lit 1048576) (nat_lit 12) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129260 BSN.pi_near_15 p129284 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129286 :=
@p129276 (nat_lit 257) (nat_lit 1048576) false (nat_lit 148998) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000) (p129258 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 41102731) (nat_lit 524288))
  (p129285 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129287 :=
p129273
  (@p129274 (nat_lit 819509) (nat_lit 3276800000)
    (@p129275 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 74499) (nat_lit 524288)
      (nat_lit 819509) (nat_lit 3276800000) (p129286 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129288 :=
@p129252 (nat_lit 486726125095) (nat_lit 1099511627776) (nat_lit 387542458317)
  (nat_lit 3435973836800000) true (nat_lit 34935337563) (nat_lit 549755813888) (nat_lit 24047783137)
  (nat_lit 214748364800000) (p129271 (Eq.refl true)) p129287

noncomputable def p129289 :=
@p129112 true (nat_lit 3540022983337663528960) (nat_lit 6439264295) (nat_lit 1099511627776)
  (nat_lit 1919935503577) (nat_lit 3435973836800000)
  (@p129113 (nat_lit 306963377177) (nat_lit 687194767360000) false (nat_lit 63431410831)
    (nat_lit 1099511627776) (nat_lit 307034194677) (nat_lit 687194767360000)
    (p129097 (nat_lit 4) (nat_lit 5) (Eq.refl true) (Eq.refl true))
    p129248)
  (p129251 p129288)

noncomputable def p129290 :=
p129289 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129291 :=
p129290 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129292 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 6)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1)))))) }

noncomputable def p129293 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 6)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129294 :=
@p129292 false (nat_lit 347262393669) (nat_lit 1099511627776) (nat_lit 70402539419)
  (nat_lit 687194767360000) false (nat_lit 284422108785) (nat_lit 1099511627776) (nat_lit 70310791919)
  (nat_lit 687194767360000) p129293

noncomputable def p129295 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1)))))))
  false

noncomputable def p129296 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1)))))
  (nat_lit 428079) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129297 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1)))))
  false (nat_lit 811211) (nat_lit 1048576)

noncomputable def p129298 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 91517983)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 91517983) (nat_lit 1048576)

noncomputable def p129299 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1))))
  false (nat_lit 196533372098742213249) (nat_lit 2251799813685248000) (nat_lit 121777500048711)

noncomputable def p129300 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0) (nat_lit 1)
  (nat_lit 4034681531866359) (nat_lit 2251799813685248)

noncomputable def p129301 :=
@p129300 (nat_lit 2500000001) (nat_lit 500000000000000) (nat_lit 196533372098742213249)
  (nat_lit 2251799813685248000) (nat_lit 121777500048711) (nat_lit 500000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 6) (nat_lit 1) (nat_lit 4034681531866359) (nat_lit 2251799813685248)
    (nat_lit 2500000001) (nat_lit 500000000000000) false
    (@p31411 (nat_lit 1000000000400000) (nat_lit 200000000000000000000) (nat_lit 4034681531866359)
      (nat_lit 2251799813685248) (nat_lit 2500000001) (nat_lit 500000000000000)
      (p31416 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129302 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 91517983)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 133669704243067041611776))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129303 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 91517983) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 13) (nat_lit 133669704243067041611776) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129304 :=
nat_lit 837532960764339607311087796291914765939330371102158480111989761792195154960640

noncomputable def p129305 :=
nat_lit 169521775065315886090697375984728583670656089197993257562866616178505441536

noncomputable def p129306 :=
nat_lit 2193264242937450364856321194536753874038969909694570696923919020648603063705856

noncomputable def p129307 :=
BSN.sin_dyadic_bound_f (nat_lit 1899560746) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129304 p31776 p129305
  p129306 p31779

noncomputable def p129308 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 1899560746)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129304 p31776 p129305 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129309 :=
p129307 p129305 (nat_lit 811211) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129308 (Eq.refl true))

noncomputable def p129310 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 1899560746)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129306 p31779 p129305 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129311 :=
@BSN.sin_arg_round false (nat_lit 811211) (nat_lit 1048576) (nat_lit 133669704243067041611776)
  (nat_lit 151115727451828646838272) (nat_lit 1899560746) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129309 (p129310 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129312 :=
p129302 (nat_lit 811211) (nat_lit 1048576) (nat_lit 13) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129303 BSN.pi_near_15 p129311 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129313 :=
@p129298 (nat_lit 1) (nat_lit 4096) false (nat_lit 811211) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129299 (nat_lit 500000000000000000) (nat_lit 91517983) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p129301 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 91517983) (nat_lit 1048576))
  (p129312 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129314 :=
@p129296 (nat_lit 1048576) (nat_lit 811211) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 347262393669) (nat_lit 1099511627776) (nat_lit 70402539419) (nat_lit 687194767360000)
  (@p31401 (nat_lit 428079) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31406
    (Eq.refl true))
  (@p129297 (nat_lit 204096) (nat_lit 819200000) (nat_lit 811211) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p129313 (Eq.refl true)) (Eq.refl true))

noncomputable def p129315 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1))))))
  (nat_lit 428079) (nat_lit 1048576)

noncomputable def p129316 :=
@p129315 (nat_lit 1) (nat_lit 1048576) (nat_lit 664415) (nat_lit 1048576) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 284422108785) (nat_lit 1099511627776) (nat_lit 70310791919) (nat_lit 687194767360000)
  (@p31401 (nat_lit 428079) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31406
    (Eq.refl true))

noncomputable def p129317 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1)))))
  true (nat_lit 664415) (nat_lit 1048576)

noncomputable def p129318 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1)))))
  true (nat_lit 664415) (nat_lit 1048576)

noncomputable def p129319 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 6) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 91517983)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 91517983) (nat_lit 1048576)

noncomputable def p129320 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 91517983)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 133669704243067041611776))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129321 :=
nat_lit 465371432324662144455533530107056971559037164429731597065577808380632199618816

noncomputable def p129322 :=
nat_lit 1395775253423855801594419195569201457509770181110798804681607691909539587973376

noncomputable def p129323 :=
BSN.cos_dyadic_bound_f (nat_lit 1899560746) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129321 p31681 p129305
  p129322 p31684

noncomputable def p129324 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1899560746)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129321 p31681 p129305 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129325 :=
p129323 p129305 (nat_lit 664415) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129324 (Eq.refl true))

noncomputable def p129326 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1899560746)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129322 p31684 p129305 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129327 :=
@BSN.cos_arg_round false (nat_lit 664415) (nat_lit 1048576) (nat_lit 133669704243067041611776)
  (nat_lit 151115727451828646838272) (nat_lit 1899560746) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129325 (p129326 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129328 :=
p129320 (nat_lit 664415) (nat_lit 1048576) (nat_lit 13) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129303 BSN.pi_near_15 p129327 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129329 :=
@p129319 (nat_lit 1) (nat_lit 4096) true (nat_lit 664415) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129299 (nat_lit 500000000000000000) (nat_lit 91517983) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p129301 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 91517983) (nat_lit 1048576))
  (p129328 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129330 :=
p129316
  (@p129317 (nat_lit 3189) (nat_lit 12800000)
    (@p129318 (nat_lit 204096) (nat_lit 819200000) (nat_lit 664415) (nat_lit 1048576) (nat_lit 3189)
      (nat_lit 12800000) (p129329 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129331 :=
@p129295 (nat_lit 347262393669) (nat_lit 1099511627776) (nat_lit 70402539419)
  (nat_lit 687194767360000) false (nat_lit 284422108785) (nat_lit 1099511627776) (nat_lit 70310791919)
  (nat_lit 687194767360000) (p129314 (Eq.refl true)) p129330

noncomputable def p129332 :=
@p129108 false (nat_lit 305645369839002572554240) (nat_lit 138991422245) (nat_lit 549755813888)
  (nat_lit 567872365793) (nat_lit 858993459200000)
  (@p129109 (nat_lit 961179672101) (nat_lit 1717986918400000) true (nat_lit 6439264295)
    (nat_lit 1099511627776) (nat_lit 1919935503577) (nat_lit 3435973836800000)
    (p129097 (nat_lit 5) (nat_lit 6) (Eq.refl true) (Eq.refl true))
    p129291)
  (p129294 p129331)

noncomputable def p129333 :=
p129332 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129334 :=
p129333 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129335 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 7)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1)))))) }

noncomputable def p129336 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 7)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129337 :=
@p129335 false (nat_lit 356577962075) (nat_lit 1099511627776) (nat_lit 327604320809)
  (nat_lit 3435973836800000) true (nat_lit 13339903175) (nat_lit 68719476736) (nat_lit 163237836967)
  (nat_lit 1717986918400000) p129336

noncomputable def p129338 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1)))))))
  false

noncomputable def p129339 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1)))))
  (nat_lit 396325) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129340 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1)))))
  false (nat_lit 899711) (nat_lit 1048576)

noncomputable def p129341 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 99391531)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 99391531) (nat_lit 1048576)

noncomputable def p129342 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1))))
  false (nat_lit 213441689007630211713) (nat_lit 2251799813685248000) (nat_lit 121777500048711)

noncomputable def p129343 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0) (nat_lit 1)
  (nat_lit 4381796493761783) (nat_lit 2251799813685248)

noncomputable def p129344 :=
@p129343 (nat_lit 2500000001) (nat_lit 500000000000000) (nat_lit 213441689007630211713)
  (nat_lit 2251799813685248000) (nat_lit 121777500048711) (nat_lit 500000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 7) (nat_lit 1) (nat_lit 4381796493761783) (nat_lit 2251799813685248)
    (nat_lit 2500000001) (nat_lit 500000000000000) false
    (@p31462 (nat_lit 1000000000400000) (nat_lit 200000000000000000000) (nat_lit 4381796493761783)
      (nat_lit 2251799813685248) (nat_lit 2500000001) (nat_lit 500000000000000)
      (p31467 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129345 :=
BSN.cos_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 99391531)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 81507407075990130655232))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129346 :=
BSN.sin_reduce_arg_pos_rat_q0 (nat_lit 99391531) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 15) (nat_lit 81507407075990130655232) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129347 :=
nat_lit 1799985918900345121926953262120960000

noncomputable def p129348 :=
BSN.cos_dyadic_bound_f (nat_lit 1158289920) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129347 p31541 p129347
  p129347 p31542

noncomputable def p129349 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 1158289920)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129347 p31541 p129347 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129350 :=
p129348 p129347 (nat_lit 899711) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129349 (Eq.refl true))

noncomputable def p129351 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 1158289920)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129347 p31542 p129347 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129352 :=
@BSN.cos_arg_round false (nat_lit 899711) (nat_lit 1048576) (nat_lit 81507407075990130655232)
  (nat_lit 151115727451828646838272) (nat_lit 1158289920) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129350 (p129351 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129353 :=
p129345 (nat_lit 899711) (nat_lit 1048576) (nat_lit 15) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129346 BSN.pi_near_15 p129352 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129354 :=
@p129341 (nat_lit 257) (nat_lit 1048576) false (nat_lit 899711) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129342 (nat_lit 500000000000000000) (nat_lit 99391531) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p129344 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 99391531) (nat_lit 1048576))
  (p129353 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129355 :=
@p129339 (nat_lit 1048576) (nat_lit 899711) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 356577962075) (nat_lit 1099511627776) (nat_lit 327604320809) (nat_lit 3435973836800000)
  (@p31452 (nat_lit 396325) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31457
    (Eq.refl true))
  (@p129340 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 899711) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p129354 (Eq.refl true))
    (Eq.refl true))

noncomputable def p129356 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 7))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1))))))
  (nat_lit 396325) (nat_lit 1048576)

noncomputable def p129357 :=
@p129356 (nat_lit 1) (nat_lit 1048576) (nat_lit 33659) (nat_lit 65536) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 13339903175) (nat_lit 68719476736) (nat_lit 163237836967) (nat_lit 1717986918400000)
  (@p31452 (nat_lit 396325) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31457
    (Eq.refl true))

noncomputable def p129358 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1)))))
  false (nat_lit 33659) (nat_lit 65536)

noncomputable def p129359 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1)))))
  false (nat_lit 538544) (nat_lit 1048576)

noncomputable def p129360 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 7) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 99391531)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 99391531) (nat_lit 1048576)

noncomputable def p129361 :=
BSN.sin_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 99391531)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 81507407075990130655232))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129362 :=
BSN.sin_dyadic_bound_f (nat_lit 1158289920) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129347 p31525 p129347
  p129347 p31526

noncomputable def p129363 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1158289920)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129347 p31525 p129347 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129364 :=
p129362 p129347 (nat_lit 538544) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129363 (Eq.refl true))

noncomputable def p129365 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1158289920)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129347 p31526 p129347 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129366 :=
@BSN.sin_arg_round false (nat_lit 538544) (nat_lit 1048576) (nat_lit 81507407075990130655232)
  (nat_lit 151115727451828646838272) (nat_lit 1158289920) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129364 (p129365 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129367 :=
p129361 (nat_lit 538544) (nat_lit 1048576) (nat_lit 15) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129346 BSN.pi_near_15 p129366 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129368 :=
@p129360 (nat_lit 257) (nat_lit 1048576) false (nat_lit 538544) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129342 (nat_lit 500000000000000000) (nat_lit 99391531) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p129344 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 99391531) (nat_lit 1048576))
  (p129367 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129369 :=
p129357
  (@p129358 (nat_lit 819509) (nat_lit 3276800000)
    (@p129359 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 33659) (nat_lit 65536)
      (nat_lit 819509) (nat_lit 3276800000) (p129368 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129370 :=
@p129338 (nat_lit 356577962075) (nat_lit 1099511627776) (nat_lit 327604320809)
  (nat_lit 3435973836800000) true (nat_lit 13339903175) (nat_lit 68719476736) (nat_lit 163237836967)
  (nat_lit 1717986918400000) (p129355 (Eq.refl true)) p129369

noncomputable def p129371 :=
@p129104 false (nat_lit 2217728480309590097920) (nat_lit 32272196845) (nat_lit 549755813888)
  (nat_lit 1298982568553) (nat_lit 1717986918400000)
  (@p129105 (nat_lit 2274372041297) (nat_lit 3435973836800000) false (nat_lit 138991422245)
    (nat_lit 549755813888) (nat_lit 567872365793) (nat_lit 858993459200000)
    (p129097 (nat_lit 6) (nat_lit 7) (Eq.refl true) (Eq.refl true))
    p129334)
  (p129337 p129370)

noncomputable def p129372 :=
p129371 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129373 :=
p129372 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129374 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 8)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1)))))) }

noncomputable def p129375 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 8)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129376 :=
@p129374 false (nat_lit 281578649037) (nat_lit 1099511627776) (nat_lit 305029941927)
  (nat_lit 3435973836800000) true (nat_lit 134004093601) (nat_lit 549755813888) (nat_lit 152457775651)
  (nat_lit 1717986918400000) p129375

noncomputable def p129377 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1)))))))
  false

noncomputable def p129378 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1)))))
  (nat_lit 370727) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129379 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1)))))
  false (nat_lit 759531) (nat_lit 1048576)

noncomputable def p129380 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 106212021)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 106212021) (nat_lit 1048576)

noncomputable def p129381 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1))))
  false (nat_lit 456177158508154130307) (nat_lit 4503599627370496000) (nat_lit 243555000146133)

noncomputable def p129382 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0) (nat_lit 1)
  (nat_lit 9364972152248037) (nat_lit 4503599627370496)

noncomputable def p129383 :=
@p129382 (nat_lit 5000000003) (nat_lit 1000000000000000) (nat_lit 456177158508154130307)
  (nat_lit 4503599627370496000) (nat_lit 243555000146133) (nat_lit 1000000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 8) (nat_lit 1) (nat_lit 9364972152248037) (nat_lit 4503599627370496)
    (nat_lit 5000000003) (nat_lit 1000000000000000) false
    (@p31515 (nat_lit 1000000000600000) (nat_lit 200000000000000000000) (nat_lit 9364972152248037)
      (nat_lit 4503599627370496) (nat_lit 5000000003) (nat_lit 1000000000000000)
      (p31520 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129384 :=
BSN.cos_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 106212021)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 114955487786399738888192))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129385 :=
BSN.sin_reduce_arg_pos_rat_q0 (nat_lit 106212021) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 16) (nat_lit 114955487786399738888192) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129386 :=
nat_lit 254515909374484044967533119839070387014726498754879232136285905814232598690625

noncomputable def p129387 :=
nat_lit 50722337928023663592612688872143279673787080763445999200940864196937890625

noncomputable def p129388 :=
nat_lit 763446283447596087575414134139466874484831922103110804410455835714303920290625

noncomputable def p129389 :=
BSN.cos_dyadic_bound_f (nat_lit 1633615735) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129386 p31681 p129387
  p129388 p31684

noncomputable def p129390 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1633615735)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129386 p31681 p129387 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129391 :=
p129389 p129387 (nat_lit 759531) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129390 (Eq.refl true))

noncomputable def p129392 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1633615735)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129388 p31684 p129387 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129393 :=
@BSN.cos_arg_round false (nat_lit 759531) (nat_lit 1048576) (nat_lit 114955487786399738888192)
  (nat_lit 151115727451828646838272) (nat_lit 1633615735) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129391 (p129392 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129394 :=
p129384 (nat_lit 759531) (nat_lit 1048576) (nat_lit 16) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129385 BSN.pi_near_15 p129393 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129395 :=
@p129380 (nat_lit 1) (nat_lit 4096) false (nat_lit 759531) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129381 (nat_lit 1000000000000000000) (nat_lit 106212021) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p129383 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 106212021) (nat_lit 1048576))
  (p129394 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129396 :=
@p129378 (nat_lit 1048576) (nat_lit 759531) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 281578649037) (nat_lit 1099511627776) (nat_lit 305029941927) (nat_lit 3435973836800000)
  (@p31505 (nat_lit 370727) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31510
    (Eq.refl true))
  (@p129379 (nat_lit 204096) (nat_lit 819200000) (nat_lit 759531) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p129395 (Eq.refl true)) (Eq.refl true))

noncomputable def p129397 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1))))))
  (nat_lit 370727) (nat_lit 1048576)

noncomputable def p129398 :=
@p129397 (nat_lit 1) (nat_lit 1048576) (nat_lit 361463) (nat_lit 524288) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 134004093601) (nat_lit 549755813888) (nat_lit 152457775651) (nat_lit 1717986918400000)
  (@p31505 (nat_lit 370727) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31510
    (Eq.refl true))

noncomputable def p129399 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1)))))
  false (nat_lit 361463) (nat_lit 524288)

noncomputable def p129400 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1)))))
  false (nat_lit 722926) (nat_lit 1048576)

noncomputable def p129401 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 8) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 106212021)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 106212021) (nat_lit 1048576)

noncomputable def p129402 :=
BSN.sin_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 106212021)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 114955487786399738888192))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129403 :=
nat_lit 7121961662914485500341661705915550625

noncomputable def p129404 :=
BSN.sin_dyadic_bound_f (nat_lit 1633615735) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129403 p31525 p129403
  p129403 p31526

noncomputable def p129405 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1633615735)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129403 p31525 p129403 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129406 :=
p129404 p129403 (nat_lit 722926) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129405 (Eq.refl true))

noncomputable def p129407 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1633615735)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129403 p31526 p129403 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129408 :=
@BSN.sin_arg_round false (nat_lit 722926) (nat_lit 1048576) (nat_lit 114955487786399738888192)
  (nat_lit 151115727451828646838272) (nat_lit 1633615735) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129406 (p129407 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129409 :=
p129402 (nat_lit 722926) (nat_lit 1048576) (nat_lit 16) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129385 BSN.pi_near_15 p129408 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129410 :=
@p129401 (nat_lit 1) (nat_lit 4096) false (nat_lit 722926) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129381 (nat_lit 1000000000000000000) (nat_lit 106212021) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p129383 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 106212021) (nat_lit 1048576))
  (p129409 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129411 :=
p129398
  (@p129399 (nat_lit 3189) (nat_lit 12800000)
    (@p129400 (nat_lit 204096) (nat_lit 819200000) (nat_lit 361463) (nat_lit 524288) (nat_lit 3189)
      (nat_lit 12800000) (p129410 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129412 :=
@p129377 (nat_lit 281578649037) (nat_lit 1099511627776) (nat_lit 305029941927)
  (nat_lit 3435973836800000) true (nat_lit 134004093601) (nat_lit 549755813888) (nat_lit 152457775651)
  (nat_lit 1717986918400000) (p129396 (Eq.refl true)) p129411

noncomputable def p129413 :=
@p129100 true (nat_lit 55927701699464766947328) (nat_lit 25432974189) (nat_lit 137438953472)
  (nat_lit 362860086051) (nat_lit 429496729600000)
  (@p129101 (nat_lit 1300988181053) (nat_lit 1717986918400000) false (nat_lit 32272196845)
    (nat_lit 549755813888) (nat_lit 1298982568553) (nat_lit 1717986918400000)
    (p129097 (nat_lit 7) (nat_lit 8) (Eq.refl true) (Eq.refl true))
    p129373)
  (p129376 p129412)

noncomputable def p129414 :=
p129413 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129415 :=
p129414 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d1196 : p129094 (nat_lit 429496729600000) :=
@p129096 (nat_lit 2907006304033) (nat_lit 3435973836800000) true (nat_lit 25432974189)
  (nat_lit 137438953472) (nat_lit 362860086051) (nat_lit 429496729600000)
  (p129097 (nat_lit 8) (nat_lit 9) (Eq.refl true) (Eq.refl true))
  p129415

noncomputable def p129416 :=
Enclosure.Complex.IsNear (p129093 (nat_lit 17)) false (nat_lit 38846079155) (nat_lit 68719476736)
  (nat_lit 611739251499) (nat_lit 429496729600000) true (nat_lit 11539536569) (nat_lit 1099511627776)
  (nat_lit 4880968540117)

noncomputable def p129417 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 17))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 16))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 16)) p129095))
  false (nat_lit 38846079155) (nat_lit 68719476736)

noncomputable def p129418 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 16))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 16)) p129095)
  false (nat_lit 896264965481) (nat_lit 1099511627776) (nat_lit 4676628822821)

noncomputable def p129419 :=
@p129418 (nat_lit 3435973836800000) true (nat_lit 623442017) (nat_lit 274877906944)
  (nat_lit 2333425269223) (nat_lit 1717986918400000) true (nat_lit 274727699001) (nat_lit 1099511627776)
  (nat_lit 217285189171) (nat_lit 3435973836800000)

noncomputable def p129420 :=
@p129419 true (nat_lit 9045768501) (nat_lit 1099511627776) (nat_lit 214118001671)
  (nat_lit 3435973836800000) false (nat_lit 683387451590870281748480) (nat_lit 38846079155) (nat_lit 68719476736)
  (nat_lit 611739251499) (nat_lit 429496729600000)

noncomputable def p129421 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 16))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 15))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 15)) p129095))
  false (nat_lit 896264965481) (nat_lit 1099511627776)

noncomputable def p129422 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 15))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 15)) p129095)
  false (nat_lit 612547890833) (nat_lit 1099511627776) (nat_lit 4452324610893)

noncomputable def p129423 :=
@p129422 (nat_lit 3435973836800000) true (nat_lit 3117508109) (nat_lit 274877906944)
  (nat_lit 2222852975759) (nat_lit 1717986918400000) false (nat_lit 35464634331) (nat_lit 137438953472)
  (nat_lit 28038026491) (nat_lit 429496729600000)

noncomputable def p129424 :=
@p129423 false (nat_lit 623516523) (nat_lit 68719476736) (nat_lit 13821536683)
  (nat_lit 214748364800000) false (nat_lit 123181718889326845100032) (nat_lit 896264965481) (nat_lit 1099511627776)
  (nat_lit 4676628822821) (nat_lit 3435973836800000)

noncomputable def p129425 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 15))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 14))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 14)) p129095))
  false (nat_lit 612547890833) (nat_lit 1099511627776)

noncomputable def p129426 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 14))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 14)) p129095)
  false (nat_lit 896956422785) (nat_lit 1099511627776) (nat_lit 4219490680697)

noncomputable def p129427 :=
@p129426 (nat_lit 3435973836800000) false (nat_lit 61442097113) (nat_lit 1099511627776)
  (nat_lit 4215219274447) (nat_lit 3435973836800000) true (nat_lit 17775533247) (nat_lit 68719476736)
  (nat_lit 58208482549) (nat_lit 858993459200000)

noncomputable def p129428 :=
@p129427 true (nat_lit 73912129549) (nat_lit 1099511627776) (nat_lit 230486677071)
  (nat_lit 3435973836800000) false (nat_lit 42093970533784211161088) (nat_lit 612547890833) (nat_lit 1099511627776)
  (nat_lit 4452324610893) (nat_lit 3435973836800000)

noncomputable def p129429 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 14))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 13))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 13)) p129095))
  false (nat_lit 896956422785) (nat_lit 1099511627776)

noncomputable def p129430 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 13))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 13)) p129095)
  false (nat_lit 167051452859) (nat_lit 274877906944) (nat_lit 1989804305453)

noncomputable def p129431 :=
@p129430 (nat_lit 1717986918400000) true (nat_lit 140219805901) (nat_lit 1099511627776)
  (nat_lit 3975628282781) (nat_lit 3435973836800000) false (nat_lit 228750611349) (nat_lit 1099511627776)
  (nat_lit 239882069791) (nat_lit 3435973836800000)

noncomputable def p129432 :=
@p129431 false (nat_lit 100830951507) (nat_lit 549755813888) (nat_lit 119795495833)
  (nat_lit 1717986918400000) false (nat_lit 246553504115118351319040) (nat_lit 896956422785)
  (nat_lit 1099511627776) (nat_lit 4219490680697) (nat_lit 3435973836800000)

noncomputable def p129433 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 13))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 12))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 12)) p129095))
  false (nat_lit 167051452859) (nat_lit 274877906944)

noncomputable def p129434 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 12))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 12)) p129095)
  false (nat_lit 348512796403) (nat_lit 549755813888) (nat_lit 466524159453)

noncomputable def p129435 :=
@p129434 (nat_lit 429496729600000) false (nat_lit 175869720167) (nat_lit 1099511627776)
  (nat_lit 3725247216249) (nat_lit 3435973836800000) true (nat_lit 14409890685) (nat_lit 549755813888)
  (nat_lit 123707667641) (nat_lit 1717986918400000)

noncomputable def p129436 :=
@p129435 true (nat_lit 79022381517) (nat_lit 274877906944) (nat_lit 62595266633)
  (nat_lit 858993459200000) false (nat_lit 183675014855344819011584) (nat_lit 167051452859) (nat_lit 274877906944)
  (nat_lit 1989804305453) (nat_lit 1717986918400000)

noncomputable def p129437 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 12))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 11))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 11)) p129095))
  false (nat_lit 348512796403) (nat_lit 549755813888)

noncomputable def p129438 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 11))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 11)) p129095)
  false (nat_lit 977036046839) (nat_lit 1099511627776) (nat_lit 3470331233577)

noncomputable def p129439 :=
@p129438 (nat_lit 3435973836800000) true (nat_lit 200191757) (nat_lit 137438953472)
  (nat_lit 866099676363) (nat_lit 858993459200000) true (nat_lit 280010454033) (nat_lit 1099511627776)
  (nat_lit 261862042047) (nat_lit 3435973836800000)

noncomputable def p129440 :=
@p129439 false (nat_lit 177471254223) (nat_lit 1099511627776) (nat_lit 260848510797)
  (nat_lit 3435973836800000) false (nat_lit 766387744147656415379456) (nat_lit 348512796403) (nat_lit 549755813888)
  (nat_lit 466524159453) (nat_lit 429496729600000)

noncomputable def p129441 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 11))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 10))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 10)) p129095))
  false (nat_lit 977036046839) (nat_lit 1099511627776)

noncomputable def p129442 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 10))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 10)) p129095)
  false (nat_lit 385446069687) (nat_lit 549755813888) (nat_lit 1598323739321)

noncomputable def p129443 :=
@p129442 (nat_lit 1717986918400000) true (nat_lit 70399153003) (nat_lit 274877906944)
  (nat_lit 1595009476821) (nat_lit 1717986918400000) false (nat_lit 206143907465) (nat_lit 1099511627776)
  (nat_lit 54736750987) (nat_lit 687194767360000)

noncomputable def p129444 :=
@p129443 false (nat_lit 69998769489) (nat_lit 274877906944) (nat_lit 27437975181)
  (nat_lit 343597383680000) false (nat_lit 537131247127888534700032) (nat_lit 977036046839) (nat_lit 1099511627776)
  (nat_lit 3470331233577) (nat_lit 3435973836800000)

noncomputable def p129445 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 10))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 9))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 9)) p129095))
  false (nat_lit 385446069687) (nat_lit 549755813888)

noncomputable def p129446 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 9))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 9)) p129095)
  false (nat_lit 412813913099) (nat_lit 1099511627776) (nat_lit 2907006304033)

noncomputable def p129447 :=
@p129446 (nat_lit 3435973836800000) true (nat_lit 25432974189) (nat_lit 137438953472)
  (nat_lit 362860086051) (nat_lit 429496729600000) false (nat_lit 358078226275) (nat_lit 1099511627776)
  (nat_lit 289641174609) (nat_lit 3435973836800000)

noncomputable def p129448 :=
@p129447 true (nat_lit 19533204625) (nat_lit 274877906944) (nat_lit 143569132617)
  (nat_lit 1717986918400000) false (nat_lit 847604871002829801652224) (nat_lit 385446069687) (nat_lit 549755813888)
  (nat_lit 1598323739321) (nat_lit 1717986918400000)

noncomputable def p129449 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 9)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1)))))) }

noncomputable def p129450 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 9)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129451 :=
@p129449 false (nat_lit 358078226275) (nat_lit 1099511627776) (nat_lit 289641174609)
  (nat_lit 3435973836800000) true (nat_lit 19533204625) (nat_lit 274877906944) (nat_lit 143569132617)
  (nat_lit 1717986918400000) p129450

noncomputable def p129452 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1)))))))
  false

noncomputable def p129453 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1)))))
  (nat_lit 349525) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129454 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1)))))
  false (nat_lit 1024471) (nat_lit 1048576)

noncomputable def p129455 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14028503)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 131072)))
  false (nat_lit 14028503) (nat_lit 131072)

noncomputable def p129456 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1))))
  false (nat_lit 482015696123260768131) (nat_lit 4503599627370496000) (nat_lit 243555000146133)

noncomputable def p129457 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0) (nat_lit 1)
  (nat_lit 9895417793173221) (nat_lit 4503599627370496)

noncomputable def p129458 :=
@p129457 (nat_lit 5000000003) (nat_lit 1000000000000000) (nat_lit 482015696123260768131)
  (nat_lit 4503599627370496000) (nat_lit 243555000146133) (nat_lit 1000000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 9) (nat_lit 1) (nat_lit 9895417793173221) (nat_lit 4503599627370496)
    (nat_lit 5000000003) (nat_lit 1000000000000000) false
    (@p31606 (nat_lit 1000000000600000) (nat_lit 200000000000000000000) (nat_lit 9895417793173221)
      (nat_lit 4503599627370496) (nat_lit 5000000003) (nat_lit 1000000000000000)
      (p31611 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129459 :=
BSN.cos_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14028503)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 131072)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4058096648403535527936))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18889465931478580854784)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129460 :=
BSN.sin_reduce_arg_pos_rat_q0 (nat_lit 14028503) (nat_lit 131072) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 17) (nat_lit 4058096648403535527936) (nat_lit 18889465931478580854784)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129461 :=
nat_lit 45303347083281171346929194437890625

noncomputable def p129462 :=
BSN.cos_dyadic_bound_f (nat_lit 461352175) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129461 p31541 p129461
  p129461 p31542

noncomputable def p129463 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 461352175)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129461 p31541 p129461 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129464 :=
p129462 p129461 (nat_lit 1024471) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129463 (Eq.refl true))

noncomputable def p129465 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 461352175)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129461 p31542 p129461 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129466 :=
@BSN.cos_arg_round false (nat_lit 1024471) (nat_lit 1048576) (nat_lit 4058096648403535527936)
  (nat_lit 18889465931478580854784) (nat_lit 461352175) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129464 (p129465 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129467 :=
p129459 (nat_lit 1024471) (nat_lit 1048576) (nat_lit 17) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129460 BSN.pi_near_15 p129466 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129468 :=
@p129455 (nat_lit 257) (nat_lit 1048576) false (nat_lit 1024471) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129456 (nat_lit 1000000000000000000) (nat_lit 14028503) (nat_lit 131072) (nat_lit 257)
    (nat_lit 1048576) p129458 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 14028503) (nat_lit 131072))
  (p129467 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129469 :=
@p129453 (nat_lit 1048576) (nat_lit 1024471) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 358078226275) (nat_lit 1099511627776) (nat_lit 289641174609) (nat_lit 3435973836800000)
  (@p31596 (nat_lit 349525) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31601
    (Eq.refl true))
  (@p129454 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 1024471) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p129468 (Eq.refl true))
    (Eq.refl true))

noncomputable def p129470 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1))))))
  (nat_lit 349525) (nat_lit 1048576)

noncomputable def p129471 :=
@p129470 (nat_lit 1) (nat_lit 1048576) (nat_lit 55885) (nat_lit 262144) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 19533204625) (nat_lit 274877906944) (nat_lit 143569132617) (nat_lit 1717986918400000)
  (@p31596 (nat_lit 349525) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31601
    (Eq.refl true))

noncomputable def p129472 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1)))))
  false (nat_lit 55885) (nat_lit 262144)

noncomputable def p129473 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1)))))
  false (nat_lit 223540) (nat_lit 1048576)

noncomputable def p129474 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 9) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14028503)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 131072)))
  false (nat_lit 14028503) (nat_lit 131072)

noncomputable def p129475 :=
BSN.sin_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14028503)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 131072)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4058096648403535527936))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18889465931478580854784)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129476 :=
BSN.sin_dyadic_bound_f (nat_lit 461352175) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129461 p31525 p129461
  p129461 p31526

noncomputable def p129477 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 461352175)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129461 p31525 p129461 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129478 :=
p129476 p129461 (nat_lit 223540) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129477 (Eq.refl true))

noncomputable def p129479 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 461352175)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129461 p31526 p129461 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129480 :=
@BSN.sin_arg_round false (nat_lit 223540) (nat_lit 1048576) (nat_lit 4058096648403535527936)
  (nat_lit 18889465931478580854784) (nat_lit 461352175) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129478 (p129479 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129481 :=
p129475 (nat_lit 223540) (nat_lit 1048576) (nat_lit 17) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129460 BSN.pi_near_15 p129480 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129482 :=
@p129474 (nat_lit 257) (nat_lit 1048576) false (nat_lit 223540) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129456 (nat_lit 1000000000000000000) (nat_lit 14028503) (nat_lit 131072) (nat_lit 257)
    (nat_lit 1048576) p129458 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 14028503) (nat_lit 131072))
  (p129481 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129483 :=
p129471
  (@p129472 (nat_lit 819509) (nat_lit 3276800000)
    (@p129473 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 55885) (nat_lit 262144)
      (nat_lit 819509) (nat_lit 3276800000) (p129482 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129484 :=
@p129452 (nat_lit 358078226275) (nat_lit 1099511627776) (nat_lit 289641174609)
  (nat_lit 3435973836800000) true (nat_lit 19533204625) (nat_lit 274877906944) (nat_lit 143569132617)
  (nat_lit 1717986918400000) (p129469 (Eq.refl true)) p129483

noncomputable def p129485 :=
@p129448 true (nat_lit 9675585914047526076416) (nat_lit 70399153003) (nat_lit 274877906944)
  (nat_lit 1595009476821) (nat_lit 1717986918400000) d1196
  (p129451 p129484) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129486 :=
p129485 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129487 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 10)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1)))))) }

noncomputable def p129488 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 10)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129489 :=
@p129487 false (nat_lit 206143907465) (nat_lit 1099511627776) (nat_lit 54736750987)
  (nat_lit 687194767360000) false (nat_lit 69998769489) (nat_lit 274877906944) (nat_lit 27437975181)
  (nat_lit 343597383680000) p129488

noncomputable def p129490 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1)))))))
  false

noncomputable def p129491 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1)))))
  (nat_lit 331589) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129492 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1)))))
  false (nat_lit 621685) (nat_lit 1048576)

noncomputable def p129493 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 58804759)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 58804759) (nat_lit 524288)

noncomputable def p129494 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1))))
  false (nat_lit 505129036246995636099) (nat_lit 4503599627370496000) (nat_lit 243555000146133)

noncomputable def p129495 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 10369917190100709) (nat_lit 4503599627370496)

noncomputable def p129496 :=
@p129495 (nat_lit 5000000003) (nat_lit 1000000000000000) (nat_lit 505129036246995636099)
  (nat_lit 4503599627370496000) (nat_lit 243555000146133) (nat_lit 1000000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 10) (nat_lit 1) (nat_lit 10369917190100709) (nat_lit 4503599627370496)
    (nat_lit 5000000003) (nat_lit 1000000000000000) false
    (@p31656 (nat_lit 1000000000600000) (nat_lit 200000000000000000000) (nat_lit 10369917190100709)
      (nat_lit 4503599627370496) (nat_lit 5000000003) (nat_lit 1000000000000000)
      (p31661 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129497 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 58804759)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 47951852159752374059008))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129498 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 58804759) (nat_lit 524288) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 17) (nat_lit 47951852159752374059008) (nat_lit 75557863725914323419136)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129499 :=
nat_lit 3450025666892185417108992742509776896

noncomputable def p129500 :=
BSN.sin_dyadic_bound_f (nat_lit 1362873608) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129499 p31525 p129499
  p129499 p31526

noncomputable def p129501 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1362873608)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129499 p31525 p129499 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129502 :=
p129500 p129499 (nat_lit 621685) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129501 (Eq.refl true))

noncomputable def p129503 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1362873608)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129499 p31526 p129499 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129504 :=
@BSN.sin_arg_round false (nat_lit 621685) (nat_lit 1048576) (nat_lit 47951852159752374059008)
  (nat_lit 75557863725914323419136) (nat_lit 1362873608) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129502 (p129503 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129505 :=
p129497 (nat_lit 621685) (nat_lit 1048576) (nat_lit 17) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129498 BSN.pi_near_15 p129504 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129506 :=
@p129493 (nat_lit 257) (nat_lit 1048576) false (nat_lit 621685) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129494 (nat_lit 1000000000000000000) (nat_lit 58804759) (nat_lit 524288) (nat_lit 257)
    (nat_lit 1048576) p129496 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 58804759) (nat_lit 524288))
  (p129505 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129507 :=
@p129491 (nat_lit 1048576) (nat_lit 621685) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 206143907465) (nat_lit 1099511627776) (nat_lit 54736750987) (nat_lit 687194767360000)
  (@p31646 (nat_lit 331589) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31651
    (Eq.refl true))
  (@p129492 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 621685) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p129506 (Eq.refl true))
    (Eq.refl true))

noncomputable def p129508 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1))))))
  (nat_lit 331589) (nat_lit 1048576)

noncomputable def p129509 :=
@p129508 (nat_lit 1) (nat_lit 1048576) (nat_lit 211101) (nat_lit 262144) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 69998769489) (nat_lit 274877906944) (nat_lit 27437975181) (nat_lit 343597383680000)
  (@p31646 (nat_lit 331589) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31651
    (Eq.refl true))

noncomputable def p129510 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1)))))
  true (nat_lit 211101) (nat_lit 262144)

noncomputable def p129511 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1)))))
  true (nat_lit 844404) (nat_lit 1048576)

noncomputable def p129512 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 10) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 58804759)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 58804759) (nat_lit 524288)

noncomputable def p129513 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 58804759)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 47951852159752374059008))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129514 :=
nat_lit 123280107163248730876983546502827823346618245669866324450116777662996384055296

noncomputable def p129515 :=
nat_lit 11902677102214868732509875780634866454131622742989253791666450147695394816

noncomputable def p129516 :=
nat_lit 369816516135541762893485619756922200306946473764112994842767000088693761376256

noncomputable def p129517 :=
BSN.cos_dyadic_bound_f (nat_lit 1362873608) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129514 p31681 p129515
  p129516 p31684

noncomputable def p129518 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1362873608)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129514 p31681 p129515 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129519 :=
p129517 p129515 (nat_lit 844404) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129518 (Eq.refl true))

noncomputable def p129520 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1362873608)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129516 p31684 p129515 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129521 :=
@BSN.cos_arg_round false (nat_lit 844404) (nat_lit 1048576) (nat_lit 47951852159752374059008)
  (nat_lit 75557863725914323419136) (nat_lit 1362873608) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129519 (p129520 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129522 :=
p129513 (nat_lit 844404) (nat_lit 1048576) (nat_lit 17) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129498 BSN.pi_near_15 p129521 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129523 :=
@p129512 (nat_lit 257) (nat_lit 1048576) true (nat_lit 844404) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129494 (nat_lit 1000000000000000000) (nat_lit 58804759) (nat_lit 524288) (nat_lit 257)
    (nat_lit 1048576) p129496 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 58804759) (nat_lit 524288))
  (p129522 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129524 :=
p129509
  (@p129510 (nat_lit 819509) (nat_lit 3276800000)
    (@p129511 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 211101) (nat_lit 262144)
      (nat_lit 819509) (nat_lit 3276800000) (p129523 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129525 :=
@p129490 (nat_lit 206143907465) (nat_lit 1099511627776) (nat_lit 54736750987)
  (nat_lit 687194767360000) false (nat_lit 69998769489) (nat_lit 274877906944) (nat_lit 27437975181)
  (nat_lit 343597383680000) (p129507 (Eq.refl true)) p129524

noncomputable def p129526 :=
@p129444 true (nat_lit 110056582303203721216) (nat_lit 200191757) (nat_lit 137438953472)
  (nat_lit 866099676363) (nat_lit 858993459200000)
  (@p129445 (nat_lit 1598323739321) (nat_lit 1717986918400000) true (nat_lit 70399153003)
    (nat_lit 274877906944) (nat_lit 1595009476821) (nat_lit 1717986918400000)
    (p129097 (nat_lit 9) (nat_lit 10) (Eq.refl true) (Eq.refl true))
    (p129486 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (p129489 p129525)

noncomputable def p129527 :=
p129526 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129528 :=
p129527 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129529 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 11)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1)))))) }

noncomputable def p129530 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 11)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129531 :=
@p129529 true (nat_lit 280010454033) (nat_lit 1099511627776) (nat_lit 261862042047)
  (nat_lit 3435973836800000) false (nat_lit 177471254223) (nat_lit 1099511627776) (nat_lit 260848510797)
  (nat_lit 3435973836800000) p129530

noncomputable def p129532 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1)))))))
  true

noncomputable def p129533 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1)))))
  (nat_lit 316157) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129534 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1)))))
  true (nat_lit 885669) (nat_lit 1048576)

noncomputable def p129535 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 122477695)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 122477695) (nat_lit 1048576)

noncomputable def p129536 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1))))
  false (nat_lit 526037698713423908739) (nat_lit 4503599627370496000) (nat_lit 243555000146133)

noncomputable def p129537 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 10799156221662949) (nat_lit 4503599627370496)

noncomputable def p129538 :=
@p129537 (nat_lit 5000000003) (nat_lit 1000000000000000) (nat_lit 526037698713423908739)
  (nat_lit 4503599627370496000) (nat_lit 243555000146133) (nat_lit 1000000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 11) (nat_lit 1) (nat_lit 10799156221662949) (nat_lit 4503599627370496)
    (nat_lit 5000000003) (nat_lit 1000000000000000) false
    (@p31712 (nat_lit 1000000000600000) (nat_lit 200000000000000000000) (nat_lit 10799156221662949)
      (nat_lit 4503599627370496) (nat_lit 5000000003) (nat_lit 1000000000000000)
      (p31717 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129539 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 122477695)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 85365859454247103365120))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129540 :=
BSN.sin_reduce_arg_pos_rat_q2 (nat_lit 122477695) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 18) (nat_lit 85365859454247103365120) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129541 :=
nat_lit 2165796591045367364569224169576924176

noncomputable def p129542 :=
BSN.cos_dyadic_bound_f (nat_lit 1213121826) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129541 p31541 p129541
  p129541 p31542

noncomputable def p129543 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 1213121826)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129541 p31541 p129541 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129544 :=
p129542 p129541 (nat_lit 885669) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129543 (Eq.refl true))

noncomputable def p129545 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 1213121826)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129541 p31542 p129541 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129546 :=
@BSN.cos_arg_round false (nat_lit 885669) (nat_lit 1048576) (nat_lit 85365859454247103365120)
  (nat_lit 151115727451828646838272) (nat_lit 1213121826) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129544 (p129545 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129547 :=
p129539 (nat_lit 885669) (nat_lit 1048576) (nat_lit 18) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129540 BSN.pi_near_15 p129546 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129548 :=
@p129535 (nat_lit 257) (nat_lit 1048576) true (nat_lit 885669) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129536 (nat_lit 1000000000000000000) (nat_lit 122477695) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p129538 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 122477695) (nat_lit 1048576))
  (p129547 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129549 :=
@p129533 (nat_lit 1048576) (nat_lit 885669) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 280010454033) (nat_lit 1099511627776) (nat_lit 261862042047) (nat_lit 3435973836800000)
  (@p31702 (nat_lit 316157) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31707
    (Eq.refl true))
  (@p129534 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 885669) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p129548 (Eq.refl true))
    (Eq.refl true))

noncomputable def p129550 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1))))))
  (nat_lit 316157) (nat_lit 1048576)

noncomputable def p129551 :=
@p129550 (nat_lit 1) (nat_lit 1048576) (nat_lit 561339) (nat_lit 1048576) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 177471254223) (nat_lit 1099511627776) (nat_lit 260848510797) (nat_lit 3435973836800000)
  (@p31702 (nat_lit 316157) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31707
    (Eq.refl true))

noncomputable def p129552 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1)))))
  true (nat_lit 561339) (nat_lit 1048576)

noncomputable def p129553 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1)))))
  true (nat_lit 561339) (nat_lit 1048576)

noncomputable def p129554 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 11) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 122477695)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 122477695) (nat_lit 1048576)

noncomputable def p129555 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 122477695)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 85365859454247103365120))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129556 :=
BSN.sin_dyadic_bound_f (nat_lit 1213121826) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129541 p31525 p129541
  p129541 p31526

noncomputable def p129557 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1213121826)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129541 p31525 p129541 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129558 :=
p129556 p129541 (nat_lit 561339) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129557 (Eq.refl true))

noncomputable def p129559 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1213121826)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129541 p31526 p129541 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129560 :=
@BSN.sin_arg_round false (nat_lit 561339) (nat_lit 1048576) (nat_lit 85365859454247103365120)
  (nat_lit 151115727451828646838272) (nat_lit 1213121826) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129558 (p129559 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129561 :=
p129555 (nat_lit 561339) (nat_lit 1048576) (nat_lit 18) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129540 BSN.pi_near_15 p129560 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129562 :=
@p129554 (nat_lit 257) (nat_lit 1048576) true (nat_lit 561339) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129536 (nat_lit 1000000000000000000) (nat_lit 122477695) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p129538 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 122477695) (nat_lit 1048576))
  (p129561 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129563 :=
p129551
  (@p129552 (nat_lit 819509) (nat_lit 3276800000)
    (@p129553 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 561339) (nat_lit 1048576)
      (nat_lit 819509) (nat_lit 3276800000) (p129562 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129564 :=
@p129532 (nat_lit 280010454033) (nat_lit 1099511627776) (nat_lit 261862042047)
  (nat_lit 3435973836800000) false (nat_lit 177471254223) (nat_lit 1099511627776) (nat_lit 260848510797)
  (nat_lit 3435973836800000) (p129549 (Eq.refl true)) p129563

noncomputable def p129565 :=
@p129440 false (nat_lit 24171350287165973069824) (nat_lit 175869720167) (nat_lit 1099511627776)
  (nat_lit 3725247216249) (nat_lit 3435973836800000)
  (@p129441 (nat_lit 3470331233577) (nat_lit 3435973836800000) true (nat_lit 200191757)
    (nat_lit 137438953472) (nat_lit 866099676363) (nat_lit 858993459200000)
    (p129097 (nat_lit 10) (nat_lit 11) (Eq.refl true) (Eq.refl true))
    p129528)
  (p129531 p129564)

noncomputable def p129566 :=
p129565 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129567 :=
p129566 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129568 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 12)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1)))))) }

noncomputable def p129569 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 12)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129570 :=
@p129568 true (nat_lit 14409890685) (nat_lit 549755813888) (nat_lit 123707667641)
  (nat_lit 1717986918400000) true (nat_lit 79022381517) (nat_lit 274877906944) (nat_lit 62595266633)
  (nat_lit 858993459200000) p129569

noncomputable def p129571 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1)))))))
  true

noncomputable def p129572 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1)))))
  (nat_lit 302697) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129573 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1)))))
  true (nat_lit 95210) (nat_lit 1048576)

noncomputable def p129574 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 63460995)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 63460995) (nat_lit 524288)

noncomputable def p129575 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1))))
  false (nat_lit 545125797033535803267) (nat_lit 4503599627370496000) (nat_lit 243555000146133)

noncomputable def p129576 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 11191020447815397) (nat_lit 4503599627370496)

noncomputable def p129577 :=
@p129576 (nat_lit 5000000003) (nat_lit 1000000000000000) (nat_lit 545125797033535803267)
  (nat_lit 4503599627370496000) (nat_lit 243555000146133) (nat_lit 1000000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 12) (nat_lit 1) (nat_lit 11191020447815397) (nat_lit 4503599627370496)
    (nat_lit 5000000003) (nat_lit 1000000000000000) false
    (@p31766 (nat_lit 1000000000600000) (nat_lit 200000000000000000000) (nat_lit 11191020447815397)
      (nat_lit 4503599627370496) (nat_lit 5000000003) (nat_lit 1000000000000000)
      (p31771 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129578 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 63460995)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6870090218509759938560))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129579 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 63460995) (nat_lit 524288) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 19) (nat_lit 6870090218509759938560) (nat_lit 75557863725914323419136)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129580 :=
BSN.sin_dyadic_bound_f (nat_lit 195259707) (nat_lit 2147483648) (nat_lit 1) (nat_lit 0) (nat_lit 1048576)
  (nat_lit 400391) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1)

noncomputable def p129581 :=
p129580 (nat_lit 1) (nat_lit 95210) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.sinEvenP (nat_lit 195259707)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))

noncomputable def p129582 :=
p129581
  (@BSN.binarySplit_of_le (BSN.sinOddP (nat_lit 195259707)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129583 :=
@BSN.sin_arg_round false (nat_lit 95210) (nat_lit 1048576) (nat_lit 6870090218509759938560)
  (nat_lit 75557863725914323419136) (nat_lit 195259707) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  p129582 (Eq.refl true)

noncomputable def p129584 :=
p129578 (nat_lit 95210) (nat_lit 1048576) (nat_lit 19) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129579 BSN.pi_near_15 p129583 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129585 :=
@p129574 (nat_lit 1) (nat_lit 4096) true (nat_lit 95210) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129575 (nat_lit 1000000000000000000) (nat_lit 63460995) (nat_lit 524288) (nat_lit 1)
    (nat_lit 4096) p129577 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 63460995) (nat_lit 524288))
  (p129584 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129586 :=
@p129572 (nat_lit 1048576) (nat_lit 47605) (nat_lit 524288) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 14409890685) (nat_lit 549755813888) (nat_lit 123707667641) (nat_lit 1717986918400000)
  (@p31756 (nat_lit 302697) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31761
    (Eq.refl true))
  (@p129573 (nat_lit 204096) (nat_lit 819200000) (nat_lit 47605) (nat_lit 524288) (nat_lit 3189)
    (nat_lit 12800000) (p129585 (Eq.refl true)) (Eq.refl true))

noncomputable def p129587 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 12))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1))))))
  (nat_lit 302697) (nat_lit 1048576)

noncomputable def p129588 :=
@p129587 (nat_lit 1) (nat_lit 1048576) (nat_lit 261061) (nat_lit 262144) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 79022381517) (nat_lit 274877906944) (nat_lit 62595266633) (nat_lit 858993459200000)
  (@p31756 (nat_lit 302697) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31761
    (Eq.refl true))

noncomputable def p129589 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1)))))
  false (nat_lit 261061) (nat_lit 262144)

noncomputable def p129590 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1)))))
  false (nat_lit 1044244) (nat_lit 1048576)

noncomputable def p129591 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 12) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 63460995)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 63460995) (nat_lit 524288)

noncomputable def p129592 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 63460995)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 6870090218509759938560))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129593 :=
nat_lit 1453618806632685943983871402770801

noncomputable def p129594 :=
BSN.cos_dyadic_bound_f (nat_lit 195259707) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129593 p31541 p129593
  p129593 p31542

noncomputable def p129595 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 195259707)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129593 p31541 p129593 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129596 :=
p129594 p129593 (nat_lit 1044244) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129595 (Eq.refl true))

noncomputable def p129597 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 195259707)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129593 p31542 p129593 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129598 :=
@BSN.cos_arg_round false (nat_lit 1044244) (nat_lit 1048576) (nat_lit 6870090218509759938560)
  (nat_lit 75557863725914323419136) (nat_lit 195259707) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129596 (p129597 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129599 :=
p129592 (nat_lit 1044244) (nat_lit 1048576) (nat_lit 19) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129579 BSN.pi_near_15 p129598 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129600 :=
@p129591 (nat_lit 1) (nat_lit 4096) false (nat_lit 1044244) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129575 (nat_lit 1000000000000000000) (nat_lit 63460995) (nat_lit 524288) (nat_lit 1)
    (nat_lit 4096) p129577 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 63460995) (nat_lit 524288))
  (p129599 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129601 :=
p129588
  (@p129589 (nat_lit 3189) (nat_lit 12800000)
    (@p129590 (nat_lit 204096) (nat_lit 819200000) (nat_lit 261061) (nat_lit 262144) (nat_lit 3189)
      (nat_lit 12800000) (p129600 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129602 :=
@p129571 (nat_lit 14409890685) (nat_lit 549755813888) (nat_lit 123707667641)
  (nat_lit 1717986918400000) true (nat_lit 79022381517) (nat_lit 274877906944) (nat_lit 62595266633)
  (nat_lit 858993459200000) (p129586 (Eq.refl true)) p129601

noncomputable def p129603 :=
@p129436 true (nat_lit 38543326758160820076544) (nat_lit 140219805901) (nat_lit 1099511627776)
  (nat_lit 3975628282781) (nat_lit 3435973836800000)
  (@p129437 (nat_lit 466524159453) (nat_lit 429496729600000) false (nat_lit 175869720167)
    (nat_lit 1099511627776) (nat_lit 3725247216249) (nat_lit 3435973836800000)
    (p129097 (nat_lit 11) (nat_lit 12) (Eq.refl true) (Eq.refl true))
    p129567)
  (p129570 p129602)

noncomputable def p129604 :=
p129603 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129605 :=
p129604 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129606 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 13)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1)))))) }

noncomputable def p129607 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 13)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129608 :=
@p129606 false (nat_lit 228750611349) (nat_lit 1099511627776) (nat_lit 239882069791)
  (nat_lit 3435973836800000) false (nat_lit 100830951507) (nat_lit 549755813888) (nat_lit 119795495833)
  (nat_lit 1717986918400000) p129607

noncomputable def p129609 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1)))))))
  false

noncomputable def p129610 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1)))))
  (nat_lit 290823) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129611 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1)))))
  false (nat_lit 786563) (nat_lit 1048576)

noncomputable def p129612 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 511759)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4096)))
  false (nat_lit 511759) (nat_lit 4096)

noncomputable def p129613 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1))))
  false (nat_lit 562684972947157225347) (nat_lit 4503599627370496000) (nat_lit 243555000146133)

noncomputable def p129614 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 11551497052968677) (nat_lit 4503599627370496)

noncomputable def p129615 :=
@p129614 (nat_lit 5000000003) (nat_lit 1000000000000000) (nat_lit 562684972947157225347)
  (nat_lit 4503599627370496000) (nat_lit 243555000146133) (nat_lit 1000000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 13) (nat_lit 1) (nat_lit 11551497052968677) (nat_lit 4503599627370496)
    (nat_lit 5000000003) (nat_lit 1000000000000000) false
    (@p31823 (nat_lit 1000000000600000) (nat_lit 200000000000000000000) (nat_lit 11551497052968677)
      (nat_lit 4503599627370496) (nat_lit 5000000003) (nat_lit 1000000000000000)
      (p31828 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129616 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 511759)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4096)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 500719774436061872128))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 590295810358705651712)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129617 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 511759) (nat_lit 4096) (nat_lit 226375608064910080) (nat_lit 72057594037927936)
  (nat_lit 19) (nat_lit 500719774436061872128) (nat_lit 590295810358705651712) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129618 :=
nat_lit 708264095781978921533754003245216314901129842168634931222892720993074427631425

noncomputable def p129619 :=
nat_lit 121238138643810248839694905131633864632177261661848648829400041787196086081

noncomputable def p129620 :=
nat_lit 1854781103394997673137900978652972465150697490113258017295185716818968040609601

noncomputable def p129621 :=
BSN.sin_dyadic_bound_f (nat_lit 1821607927) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129618 p31776 p129619
  p129620 p31779

noncomputable def p129622 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 1821607927)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129618 p31776 p129619 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129623 :=
p129621 p129619 (nat_lit 786563) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129622 (Eq.refl true))

noncomputable def p129624 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 1821607927)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129620 p31779 p129619 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129625 :=
@BSN.sin_arg_round false (nat_lit 786563) (nat_lit 1048576) (nat_lit 500719774436061872128)
  (nat_lit 590295810358705651712) (nat_lit 1821607927) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129623 (p129624 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129626 :=
p129616 (nat_lit 786563) (nat_lit 1048576) (nat_lit 19) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129617 BSN.pi_near_15 p129625 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129627 :=
@p129612 (nat_lit 1) (nat_lit 4096) false (nat_lit 786563) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129613 (nat_lit 1000000000000000000) (nat_lit 511759) (nat_lit 4096) (nat_lit 1) (nat_lit 4096)
    p129615 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 511759) (nat_lit 4096))
  (p129626 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129628 :=
@p129610 (nat_lit 1048576) (nat_lit 786563) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 228750611349) (nat_lit 1099511627776) (nat_lit 239882069791) (nat_lit 3435973836800000)
  (@p31813 (nat_lit 290823) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31818
    (Eq.refl true))
  (@p129611 (nat_lit 204096) (nat_lit 819200000) (nat_lit 786563) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p129627 (Eq.refl true)) (Eq.refl true))

noncomputable def p129629 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 13))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1))))))
  (nat_lit 290823) (nat_lit 1048576)

noncomputable def p129630 :=
@p129629 (nat_lit 1) (nat_lit 1048576) (nat_lit 346709) (nat_lit 524288) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 100830951507) (nat_lit 549755813888) (nat_lit 119795495833) (nat_lit 1717986918400000)
  (@p31813 (nat_lit 290823) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31818
    (Eq.refl true))

noncomputable def p129631 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1)))))
  true (nat_lit 346709) (nat_lit 524288)

noncomputable def p129632 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1)))))
  true (nat_lit 693418) (nat_lit 1048576)

noncomputable def p129633 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 13) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 511759)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4096)))
  false (nat_lit 511759) (nat_lit 4096)

noncomputable def p129634 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 511759)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 4096)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 500719774436061872128))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 590295810358705651712)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129635 :=
nat_lit 393533936829385538740458755094067567773797546654424672301086800570280102500161

noncomputable def p129636 :=
nat_lit 1180359334210868995723696875471939435592128285439950319605601601627265915328321

noncomputable def p129637 :=
BSN.cos_dyadic_bound_f (nat_lit 1821607927) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129635 p31681 p129619
  p129636 p31684

noncomputable def p129638 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1821607927)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129635 p31681 p129619 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129639 :=
p129637 p129619 (nat_lit 693418) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129638 (Eq.refl true))

noncomputable def p129640 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1821607927)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129636 p31684 p129619 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129641 :=
@BSN.cos_arg_round false (nat_lit 693418) (nat_lit 1048576) (nat_lit 500719774436061872128)
  (nat_lit 590295810358705651712) (nat_lit 1821607927) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129639 (p129640 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129642 :=
p129634 (nat_lit 693418) (nat_lit 1048576) (nat_lit 19) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129617 BSN.pi_near_15 p129641 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129643 :=
@p129633 (nat_lit 1) (nat_lit 4096) true (nat_lit 693418) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129613 (nat_lit 1000000000000000000) (nat_lit 511759) (nat_lit 4096) (nat_lit 1) (nat_lit 4096)
    p129615 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 511759) (nat_lit 4096))
  (p129642 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129644 :=
p129630
  (@p129631 (nat_lit 3189) (nat_lit 12800000)
    (@p129632 (nat_lit 204096) (nat_lit 819200000) (nat_lit 346709) (nat_lit 524288) (nat_lit 3189)
      (nat_lit 12800000) (p129643 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129645 :=
@p129609 (nat_lit 228750611349) (nat_lit 1099511627776) (nat_lit 239882069791)
  (nat_lit 3435973836800000) false (nat_lit 100830951507) (nat_lit 549755813888) (nat_lit 119795495833)
  (nat_lit 1717986918400000) (p129628 (Eq.refl true)) p129644

noncomputable def p129646 :=
@p129432 false (nat_lit 33778150105342850105344) (nat_lit 61442097113) (nat_lit 1099511627776)
  (nat_lit 4215219274447) (nat_lit 3435973836800000)
  (@p129433 (nat_lit 1989804305453) (nat_lit 1717986918400000) true (nat_lit 140219805901)
    (nat_lit 1099511627776) (nat_lit 3975628282781) (nat_lit 3435973836800000)
    (p129097 (nat_lit 12) (nat_lit 13) (Eq.refl true) (Eq.refl true))
    p129605)
  (p129608 p129645)

noncomputable def p129647 :=
p129646 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129648 :=
p129647 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129649 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 14)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1)))))) }

noncomputable def p129650 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 14)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129651 :=
@p129649 true (nat_lit 17775533247) (nat_lit 68719476736) (nat_lit 58208482549)
  (nat_lit 858993459200000) true (nat_lit 73912129549) (nat_lit 1099511627776) (nat_lit 230486677071)
  (nat_lit 3435973836800000) p129650

noncomputable def p129652 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1)))))))
  true

noncomputable def p129653 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1)))))
  (nat_lit 280243) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129654 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1)))))
  true (nat_lit 1014864) (nat_lit 1048576)

noncomputable def p129655 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 67397769)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 67397769) (nat_lit 524288)

noncomputable def p129656 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1))))
  false (nat_lit 115788486170262360039) (nat_lit 900719925474099200) (nat_lit 243555000146133)

noncomputable def p129657 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 11885250371606245) (nat_lit 4503599627370496)

noncomputable def p129658 :=
@p129657 (nat_lit 5000000003) (nat_lit 1000000000000000) (nat_lit 115788486170262360039)
  (nat_lit 900719925474099200) (nat_lit 243555000146133) (nat_lit 1000000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 14) (nat_lit 1) (nat_lit 11885250371606245) (nat_lit 4503599627370496)
    (nat_lit 5000000003) (nat_lit 1000000000000000) false
    (@p31878 (nat_lit 1000000000600000) (nat_lit 200000000000000000000) (nat_lit 11885250371606245)
      (nat_lit 4503599627370496) (nat_lit 5000000003) (nat_lit 1000000000000000)
      (p31883 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129659 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 67397769)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 99474956436106880483328))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129660 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 67397769) (nat_lit 524288) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 20) (nat_lit 99474956436106880483328) (nat_lit 75557863725914323419136)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129661 :=
nat_lit 4113280285569831090304050334781541351664305827460772929386146776901021823345185

noncomputable def p129662 :=
nat_lit 4082363021308083727250857611996442740612843004207289766591979579429440660001

noncomputable def p129663 :=
nat_lit 10766267398267439767618868535913185489921713516580926822103521210659790442930721

noncomputable def p129664 :=
BSN.sin_dyadic_bound_f (nat_lit 2827248307) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129661 p31776 p129662
  p129663 p31779

noncomputable def p129665 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 2827248307)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129661 p31776 p129662 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129666 :=
p129664 p129662 (nat_lit 1014864) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129665 (Eq.refl true))

noncomputable def p129667 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 2827248307)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129663 p31779 p129662 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129668 :=
@BSN.sin_arg_round false (nat_lit 1014864) (nat_lit 1048576) (nat_lit 99474956436106880483328)
  (nat_lit 75557863725914323419136) (nat_lit 2827248307) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129666 (p129667 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129669 :=
p129659 (nat_lit 1014864) (nat_lit 1048576) (nat_lit 20) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129660 BSN.pi_near_15 p129668 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129670 :=
@p129655 (nat_lit 257) (nat_lit 1048576) true (nat_lit 1014864) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129656 (nat_lit 1000000000000000000) (nat_lit 67397769) (nat_lit 524288) (nat_lit 257)
    (nat_lit 1048576) p129658 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 67397769) (nat_lit 524288))
  (p129669 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129671 :=
@p129653 (nat_lit 1048576) (nat_lit 63429) (nat_lit 65536) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 17775533247) (nat_lit 68719476736) (nat_lit 58208482549) (nat_lit 858993459200000)
  (@p31868 (nat_lit 280243) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31873
    (Eq.refl true))
  (@p129654 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 63429) (nat_lit 65536) (nat_lit 819509)
    (nat_lit 3276800000) (p129670 (Eq.refl true)) (Eq.refl true))

noncomputable def p129672 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1))))))
  (nat_lit 280243) (nat_lit 1048576)

noncomputable def p129673 :=
@p129672 (nat_lit 1) (nat_lit 1048576) (nat_lit 263743) (nat_lit 1048576) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 73912129549) (nat_lit 1099511627776) (nat_lit 230486677071) (nat_lit 3435973836800000)
  (@p31868 (nat_lit 280243) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31873
    (Eq.refl true))

noncomputable def p129674 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1)))))
  false (nat_lit 263743) (nat_lit 1048576)

noncomputable def p129675 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1)))))
  false (nat_lit 263743) (nat_lit 1048576)

noncomputable def p129676 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 14) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 67397769)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 67397769) (nat_lit 524288)

noncomputable def p129677 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 67397769)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 99474956436106880483328))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129678 :=
nat_lit 2286970097770487531825472789372854725475997834368965978444122422535869653262881

noncomputable def p129679 :=
nat_lit 6852745567268846428021916652894571290946767817098483355799183308448750078468641

noncomputable def p129680 :=
BSN.cos_dyadic_bound_f (nat_lit 2827248307) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129678 p31681 p129662
  p129679 p31684

noncomputable def p129681 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 2827248307)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129678 p31681 p129662 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129682 :=
p129680 p129662 (nat_lit 263743) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129681 (Eq.refl true))

noncomputable def p129683 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 2827248307)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129679 p31684 p129662 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129684 :=
@BSN.cos_arg_round false (nat_lit 263743) (nat_lit 1048576) (nat_lit 99474956436106880483328)
  (nat_lit 75557863725914323419136) (nat_lit 2827248307) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129682 (p129683 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129685 :=
p129677 (nat_lit 263743) (nat_lit 1048576) (nat_lit 20) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129660 BSN.pi_near_15 p129684 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129686 :=
@p129676 (nat_lit 257) (nat_lit 1048576) false (nat_lit 263743) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129656 (nat_lit 1000000000000000000) (nat_lit 67397769) (nat_lit 524288) (nat_lit 257)
    (nat_lit 1048576) p129658 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 67397769) (nat_lit 524288))
  (p129685 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129687 :=
p129673
  (@p129674 (nat_lit 819509) (nat_lit 3276800000)
    (@p129675 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 263743) (nat_lit 1048576)
      (nat_lit 819509) (nat_lit 3276800000) (p129686 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129688 :=
@p129652 (nat_lit 17775533247) (nat_lit 68719476736) (nat_lit 58208482549) (nat_lit 858993459200000)
  true (nat_lit 73912129549) (nat_lit 1099511627776) (nat_lit 230486677071) (nat_lit 3435973836800000)
  (p129671 (Eq.refl true)) p129687

noncomputable def p129689 :=
@p129428 true (nat_lit 13710945662125878542336) (nat_lit 3117508109) (nat_lit 274877906944)
  (nat_lit 2222852975759) (nat_lit 1717986918400000)
  (@p129429 (nat_lit 4219490680697) (nat_lit 3435973836800000) false (nat_lit 61442097113)
    (nat_lit 1099511627776) (nat_lit 4215219274447) (nat_lit 3435973836800000)
    (p129097 (nat_lit 13) (nat_lit 14) (Eq.refl true) (Eq.refl true))
    p129648)
  (p129651 p129688)

noncomputable def p129690 :=
p129689 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129691 :=
p129690 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129692 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 15)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1)))))) }

noncomputable def p129693 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 15)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129694 :=
@p129692 false (nat_lit 35464634331) (nat_lit 137438953472) (nat_lit 28038026491)
  (nat_lit 429496729600000) false (nat_lit 623516523) (nat_lit 68719476736) (nat_lit 13821536683)
  (nat_lit 214748364800000) p129693

noncomputable def p129695 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1)))))))
  false

noncomputable def p129696 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1)))))
  (nat_lit 270741) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129697 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1)))))
  false (nat_lit 1047928) (nat_lit 1048576)

noncomputable def p129698 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 138319487)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 138319487) (nat_lit 1048576)

noncomputable def p129699 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1))))
  false (nat_lit 594077674772377309059) (nat_lit 4503599627370496000) (nat_lit 243555000146133)

noncomputable def p129700 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 12195965485668069) (nat_lit 4503599627370496)

noncomputable def p129701 :=
@p129700 (nat_lit 5000000003) (nat_lit 1000000000000000) (nat_lit 594077674772377309059)
  (nat_lit 4503599627370496000) (nat_lit 243555000146133) (nat_lit 1000000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 15) (nat_lit 1) (nat_lit 12195965485668069) (nat_lit 4503599627370496)
    (nat_lit 5000000003) (nat_lit 1000000000000000) false
    (@p31933 (nat_lit 1000000000600000) (nat_lit 200000000000000000000) (nat_lit 12195965485668069)
      (nat_lit 4503599627370496) (nat_lit 5000000003) (nat_lit 1000000000000000)
      (p31938 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129702 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 138319487)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 232060426572395681153024))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129703 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 138319487) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 20) (nat_lit 232060426572395681153024) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129704 :=
nat_lit 7620515133126941269413036209848291610633692436775426943039291613455485265555585

noncomputable def p129705 :=
nat_lit 13988472238779045752714060368698533588801749474299763371984510400728705052801

noncomputable def p129706 :=
nat_lit 19935844012660156298196414928053347068706372597167728091072074542210805411131521

noncomputable def p129707 :=
BSN.sin_dyadic_bound_f (nat_lit 3297777007) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129704 p31776 p129705
  p129706 p31779

noncomputable def p129708 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 3297777007)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129704 p31776 p129705 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129709 :=
p129707 p129705 (nat_lit 1047928) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129708 (Eq.refl true))

noncomputable def p129710 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 3297777007)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129706 p31779 p129705 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129711 :=
@BSN.sin_arg_round false (nat_lit 1047928) (nat_lit 1048576) (nat_lit 232060426572395681153024)
  (nat_lit 151115727451828646838272) (nat_lit 3297777007) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129709 (p129710 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129712 :=
p129702 (nat_lit 1047928) (nat_lit 1048576) (nat_lit 20) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129703 BSN.pi_near_15 p129711 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129713 :=
@p129698 (nat_lit 1) (nat_lit 4096) false (nat_lit 1047928) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129699 (nat_lit 1000000000000000000) (nat_lit 138319487) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p129701 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 138319487) (nat_lit 1048576))
  (p129712 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129714 :=
@p129696 (nat_lit 1048576) (nat_lit 130991) (nat_lit 131072) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 35464634331) (nat_lit 137438953472) (nat_lit 28038026491) (nat_lit 429496729600000)
  (@p31923 (nat_lit 270741) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31928
    (Eq.refl true))
  (@p129697 (nat_lit 204096) (nat_lit 819200000) (nat_lit 130991) (nat_lit 131072) (nat_lit 3189)
    (nat_lit 12800000) (p129713 (Eq.refl true)) (Eq.refl true))

noncomputable def p129715 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 15))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1))))))
  (nat_lit 270741) (nat_lit 1048576)

noncomputable def p129716 :=
@p129715 (nat_lit 1) (nat_lit 1048576) (nat_lit 2303) (nat_lit 65536) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 623516523) (nat_lit 68719476736) (nat_lit 13821536683) (nat_lit 214748364800000)
  (@p31923 (nat_lit 270741) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31928
    (Eq.refl true))

noncomputable def p129717 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1)))))
  true (nat_lit 2303) (nat_lit 65536)

noncomputable def p129718 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1)))))
  true (nat_lit 36848) (nat_lit 1048576)

noncomputable def p129719 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 15) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 138319487)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 138319487) (nat_lit 1048576)

noncomputable def p129720 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 138319487)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 232060426572395681153024))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129721 :=
nat_lit 4239836617176646947786226365635139131947074353530481529853821789875593460887681

noncomputable def p129722 :=
nat_lit 12691532907052382751853250976168020328663619561642845062817496348825322972557441

noncomputable def p129723 :=
BSN.cos_dyadic_bound_f (nat_lit 3297777007) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129721 p31681 p129705
  p129722 p31684

noncomputable def p129724 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 3297777007)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129721 p31681 p129705 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129725 :=
p129723 p129705 (nat_lit 36848) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129724 (Eq.refl true))

noncomputable def p129726 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 3297777007)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129722 p31684 p129705 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129727 :=
@BSN.cos_arg_round false (nat_lit 36848) (nat_lit 1048576) (nat_lit 232060426572395681153024)
  (nat_lit 151115727451828646838272) (nat_lit 3297777007) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129725 (p129726 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129728 :=
p129720 (nat_lit 36848) (nat_lit 1048576) (nat_lit 20) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129703 BSN.pi_near_15 p129727 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129729 :=
@p129719 (nat_lit 1) (nat_lit 4096) true (nat_lit 36848) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129699 (nat_lit 1000000000000000000) (nat_lit 138319487) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p129701 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 138319487) (nat_lit 1048576))
  (p129728 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129730 :=
p129716
  (@p129717 (nat_lit 3189) (nat_lit 12800000)
    (@p129718 (nat_lit 204096) (nat_lit 819200000) (nat_lit 2303) (nat_lit 65536) (nat_lit 3189)
      (nat_lit 12800000) (p129729 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129731 :=
@p129695 (nat_lit 35464634331) (nat_lit 137438953472) (nat_lit 28038026491) (nat_lit 429496729600000)
  false (nat_lit 623516523) (nat_lit 68719476736) (nat_lit 13821536683) (nat_lit 214748364800000)
  (p129714 (Eq.refl true)) p129730

noncomputable def p129732 :=
@p129424 true (nat_lit 42842609183476416512) (nat_lit 623442017) (nat_lit 274877906944)
  (nat_lit 2333425269223) (nat_lit 1717986918400000)
  (@p129425 (nat_lit 4452324610893) (nat_lit 3435973836800000) true (nat_lit 3117508109)
    (nat_lit 274877906944) (nat_lit 2222852975759) (nat_lit 1717986918400000)
    (p129097 (nat_lit 14) (nat_lit 15) (Eq.refl true) (Eq.refl true))
    p129691)
  (p129694 p129731)

noncomputable def p129733 :=
p129732 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129734 :=
p129733 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129735 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 16)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1)))))) }

noncomputable def p129736 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 16)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129737 :=
@p129735 true (nat_lit 274727699001) (nat_lit 1099511627776) (nat_lit 217285189171)
  (nat_lit 3435973836800000) true (nat_lit 9045768501) (nat_lit 1099511627776) (nat_lit 214118001671)
  (nat_lit 3435973836800000) p129736

noncomputable def p129738 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1)))))))
  true

noncomputable def p129739 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1)))))
  (nat_lit 262143) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129740 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1)))))
  true (nat_lit 1048007) (nat_lit 1048576)

noncomputable def p129741 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35404007)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  false (nat_lit 35404007) (nat_lit 262144)

noncomputable def p129742 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1))))
  false (nat_lit 152059052836051376769) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p129743 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3121657384082679) (nat_lit 1125899906842624)

noncomputable def p129744 :=
@p129743 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 152059052836051376769)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 16) (nat_lit 1) (nat_lit 3121657384082679) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p31988 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3121657384082679)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p31993 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129745 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35404007)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 58099498395655842299904))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37778931862957161709568)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129746 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 35404007) (nat_lit 262144) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 21) (nat_lit 58099498395655842299904) (nat_lit 37778931862957161709568)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129747 :=
nat_lit 7665034787661213956160624076586135592604608953707546865340079533533273491267840

noncomputable def p129748 :=
nat_lit 14152090221150647618232673889591455110252049065756388154961988592137526599936

noncomputable def p129749 :=
nat_lit 20052178202564173598562591109523397529500234418365683828401698415818922195968256

noncomputable def p129750 :=
BSN.sin_dyadic_bound_f (nat_lit 3302574122) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129747 p31776 p129748
  p129749 p31779

noncomputable def p129751 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 3302574122)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129747 p31776 p129748 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129752 :=
p129750 p129748 (nat_lit 1048007) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129751 (Eq.refl true))

noncomputable def p129753 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 3302574122)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129749 p31779 p129748 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129754 :=
@BSN.sin_arg_round false (nat_lit 1048007) (nat_lit 1048576) (nat_lit 58099498395655842299904)
  (nat_lit 37778931862957161709568) (nat_lit 3302574122) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129752 (p129753 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129755 :=
p129745 (nat_lit 1048007) (nat_lit 1048576) (nat_lit 21) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129746 BSN.pi_near_15 p129754 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129756 :=
@p129741 (nat_lit 1) (nat_lit 4096) true (nat_lit 1048007) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129742 (nat_lit 250000000000000000) (nat_lit 35404007) (nat_lit 262144) (nat_lit 1)
    (nat_lit 4096) p129744 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 35404007) (nat_lit 262144))
  (p129755 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129757 :=
@p129739 (nat_lit 1048576) (nat_lit 1048007) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 274727699001) (nat_lit 1099511627776) (nat_lit 217285189171) (nat_lit 3435973836800000)
  (@p31978 (nat_lit 262143) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31983
    (Eq.refl true))
  (@p129740 (nat_lit 204096) (nat_lit 819200000) (nat_lit 1048007) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p129756 (Eq.refl true)) (Eq.refl true))

noncomputable def p129758 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 16))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1))))))
  (nat_lit 262143) (nat_lit 1048576)

noncomputable def p129759 :=
@p129758 (nat_lit 1) (nat_lit 1048576) (nat_lit 34507) (nat_lit 1048576) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 9045768501) (nat_lit 1099511627776) (nat_lit 214118001671) (nat_lit 3435973836800000)
  (@p31978 (nat_lit 262143) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p31983
    (Eq.refl true))

noncomputable def p129760 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1)))))
  false (nat_lit 34507) (nat_lit 1048576)

noncomputable def p129761 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1)))))
  false (nat_lit 34507) (nat_lit 1048576)

noncomputable def p129762 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 16) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35404007)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  false (nat_lit 35404007) (nat_lit 262144)

noncomputable def p129763 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35404007)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 58099498395655842299904))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37778931862957161709568)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129764 :=
nat_lit 4264642477687852485697339008721004864829339218311195542146693958003879729193216

noncomputable def p129765 :=
nat_lit 12765623252621256161855551678383831684267513556802073850130157896827364134379776

noncomputable def p129766 :=
BSN.cos_dyadic_bound_f (nat_lit 3302574122) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129764 p31681 p129748
  p129765 p31684

noncomputable def p129767 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 3302574122)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129764 p31681 p129748 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129768 :=
p129766 p129748 (nat_lit 34507) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129767 (Eq.refl true))

noncomputable def p129769 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 3302574122)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129765 p31684 p129748 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129770 :=
@BSN.cos_arg_round false (nat_lit 34507) (nat_lit 1048576) (nat_lit 58099498395655842299904)
  (nat_lit 37778931862957161709568) (nat_lit 3302574122) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129768 (p129769 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129771 :=
p129763 (nat_lit 34507) (nat_lit 1048576) (nat_lit 21) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129746 BSN.pi_near_15 p129770 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129772 :=
@p129762 (nat_lit 1) (nat_lit 4096) false (nat_lit 34507) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129742 (nat_lit 250000000000000000) (nat_lit 35404007) (nat_lit 262144) (nat_lit 1)
    (nat_lit 4096) p129744 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 35404007) (nat_lit 262144))
  (p129771 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129773 :=
p129759
  (@p129760 (nat_lit 3189) (nat_lit 12800000)
    (@p129761 (nat_lit 204096) (nat_lit 819200000) (nat_lit 34507) (nat_lit 1048576) (nat_lit 3189)
      (nat_lit 12800000) (p129772 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129774 :=
@p129738 (nat_lit 274727699001) (nat_lit 1099511627776) (nat_lit 217285189171)
  (nat_lit 3435973836800000) true (nat_lit 9045768501) (nat_lit 1099511627776) (nat_lit 214118001671)
  (nat_lit 3435973836800000) (p129757 (Eq.refl true)) p129773

noncomputable def p129775 :=
@p129420 true (nat_lit 3171963659190467035136) (nat_lit 11539536569) (nat_lit 1099511627776)
  (nat_lit 4880968540117) (nat_lit 3435973836800000)
  (@p129421 (nat_lit 4676628822821) (nat_lit 3435973836800000) true (nat_lit 623442017)
    (nat_lit 274877906944) (nat_lit 2333425269223) (nat_lit 1717986918400000)
    (p129097 (nat_lit 15) (nat_lit 16) (Eq.refl true) (Eq.refl true))
    p129734)
  (p129737 p129774)

noncomputable def p129776 :=
p129775 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129777 :=
p129776 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d1197 : p129416 (nat_lit 3435973836800000) :=
@p129417 (nat_lit 611739251499) (nat_lit 429496729600000) true (nat_lit 11539536569)
  (nat_lit 1099511627776) (nat_lit 4880968540117) (nat_lit 3435973836800000)
  (p129097 (nat_lit 16) (nat_lit 17) (Eq.refl true) (Eq.refl true))
  p129777

noncomputable def p129778 :=
Enclosure.Complex.IsNear (p129093 (nat_lit 25)) false (nat_lit 39429631493) (nat_lit 68719476736)
  (nat_lit 128710925751) (nat_lit 68719476736000) false (nat_lit 20347977125) (nat_lit 549755813888)
  (nat_lit 128436149751)

noncomputable def p129779 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 25))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 24))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 24)) p129095))
  false (nat_lit 39429631493) (nat_lit 68719476736)

noncomputable def p129780 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 24))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 24)) p129095)
  false (nat_lit 775922983213) (nat_lit 1099511627776) (nat_lit 1251737944363)

noncomputable def p129781 :=
@p129780 (nat_lit 687194767360000) true (nat_lit 4080336757) (nat_lit 34359738368)
  (nat_lit 39028550859) (nat_lit 21474836480000) true (nat_lit 145048879325) (nat_lit 1099511627776)
  (nat_lit 35371313147) (nat_lit 687194767360000)

noncomputable def p129782 :=
@p129781 false (nat_lit 85633365237) (nat_lit 549755813888) (nat_lit 17723935011)
  (nat_lit 343597383680000) false (nat_lit 693653412887620210393088) (nat_lit 39429631493) (nat_lit 68719476736)
  (nat_lit 128710925751) (nat_lit 68719476736000)

noncomputable def p129783 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 24))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 23))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 23)) p129095))
  false (nat_lit 775922983213) (nat_lit 1099511627776)

noncomputable def p129784 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 23))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 23)) p129095)
  false (nat_lit 428956507499) (nat_lit 549755813888) (nat_lit 1519584284161)

noncomputable def p129785 :=
@p129784 (nat_lit 858993459200000) false (nat_lit 83530790023) (nat_lit 1099511627776)
  (nat_lit 6062327321019) (nat_lit 3435973836800000) true (nat_lit 81990031785) (nat_lit 1099511627776)
  (nat_lit 180352585171) (nat_lit 3435973836800000)

noncomputable def p129786 :=
@p129785 true (nat_lit 214101566247) (nat_lit 1099511627776) (nat_lit 182240816421)
  (nat_lit 3435973836800000) false (nat_lit 426568171150667776262144) (nat_lit 775922983213)
  (nat_lit 1099511627776) (nat_lit 1251737944363) (nat_lit 687194767360000)

noncomputable def p129787 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 23))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 22))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 22)) p129095))
  false (nat_lit 428956507499) (nat_lit 549755813888)

noncomputable def p129788 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 22))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 22)) p129095)
  false (nat_lit 629601628279) (nat_lit 1099511627776) (nat_lit 5892636502997)

noncomputable def p129789 :=
@p129788 (nat_lit 3435973836800000) false (nat_lit 30381007501) (nat_lit 1099511627776)
  (nat_lit 5879075190497) (nat_lit 3435973836800000) false (nat_lit 228311386719) (nat_lit 1099511627776)
  (nat_lit 185700633647) (nat_lit 3435973836800000)

noncomputable def p129790 :=
@p129789 false (nat_lit 26574891261) (nat_lit 549755813888) (nat_lit 91626065261)
  (nat_lit 1717986918400000) false (nat_lit 943285335610666881384448) (nat_lit 428956507499) (nat_lit 549755813888)
  (nat_lit 1519584284161) (nat_lit 858993459200000)

noncomputable def p129791 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 22))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 21))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 21)) p129095))
  false (nat_lit 629601628279) (nat_lit 1099511627776)

noncomputable def p129792 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 21))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 21)) p129095)
  false (nat_lit 821068750867) (nat_lit 1099511627776) (nat_lit 5700601728617)

noncomputable def p129793 :=
@p129792 (nat_lit 3435973836800000) true (nat_lit 114215493603) (nat_lit 1099511627776)
  (nat_lit 5688320653617) (nat_lit 3435973836800000) true (nat_lit 47866780647) (nat_lit 274877906944)
  (nat_lit 9601738719) (nat_lit 171798691840000)

noncomputable def p129794 :=
@p129793 false (nat_lit 9037281319) (nat_lit 68719476736) (nat_lit 2384431711)
  (nat_lit 42949672960000) false (nat_lit 173063577789865840869376) (nat_lit 629601628279) (nat_lit 1099511627776)
  (nat_lit 5892636502997) (nat_lit 3435973836800000)

noncomputable def p129795 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 21))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 20))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 20)) p129095))
  false (nat_lit 821068750867) (nat_lit 1099511627776)

noncomputable def p129796 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 20))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 20)) p129095)
  false (nat_lit 195536079427) (nat_lit 274877906944) (nat_lit 1376983167253)

noncomputable def p129797 :=
@p129796 (nat_lit 858993459200000) false (nat_lit 8033888751) (nat_lit 68719476736)
  (nat_lit 343308431657) (nat_lit 214748364800000) false (nat_lit 38924433159) (nat_lit 1099511627776)
  (nat_lit 38533811921) (nat_lit 687194767360000)

noncomputable def p129798 :=
@p129797 true (nat_lit 242757713619) (nat_lit 1099511627776) (nat_lit 39077149421)
  (nat_lit 687194767360000) false (nat_lit 225693659695445545320448) (nat_lit 821068750867) (nat_lit 1099511627776)
  (nat_lit 5700601728617) (nat_lit 3435973836800000)

noncomputable def p129799 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 20))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 19))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 19)) p129095))
  false (nat_lit 195536079427) (nat_lit 274877906944)

noncomputable def p129800 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 19))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 19)) p129095)
  false (nat_lit 332373597823) (nat_lit 549755813888) (nat_lit 2655009138861)

noncomputable def p129801 :=
@p129800 (nat_lit 1717986918400000) true (nat_lit 94717941735) (nat_lit 1099511627776)
  (nat_lit 5293645293347) (nat_lit 3435973836800000) false (nat_lit 58698561031) (nat_lit 549755813888)
  (nat_lit 19791439129) (nat_lit 343597383680000)

noncomputable def p129802 :=
@p129801 false (nat_lit 223260161751) (nat_lit 1099511627776) (nat_lit 39857922633)
  (nat_lit 687194767360000) false (nat_lit 214994192979717995364352) (nat_lit 195536079427) (nat_lit 274877906944)
  (nat_lit 1376983167253) (nat_lit 858993459200000)

noncomputable def p129803 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 19))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 18))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 18)) p129095))
  false (nat_lit 332373597823) (nat_lit 549755813888)

noncomputable def p129804 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 18))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 18)) p129095)
  false (nat_lit 881693130483) (nat_lit 1099511627776) (nat_lit 5104731904979)

noncomputable def p129805 :=
@p129804 (nat_lit 3435973836800000) false (nat_lit 5880520575) (nat_lit 137438953472)
  (nat_lit 2544654775927) (nat_lit 1717986918400000) true (nat_lit 216945934837) (nat_lit 1099511627776)
  (nat_lit 205286372743) (nat_lit 3435973836800000)

noncomputable def p129806 :=
@p129805 true (nat_lit 141762106335) (nat_lit 1099511627776) (nat_lit 204335741493)
  (nat_lit 3435973836800000) false (nat_lit 730897271144264599863296) (nat_lit 332373597823) (nat_lit 549755813888)
  (nat_lit 2655009138861) (nat_lit 1717986918400000)

noncomputable def p129807 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 18))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 17))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 17)) p129095))
  false (nat_lit 881693130483) (nat_lit 1099511627776)

noncomputable def p129808 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 17))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 17)) p129095)
  false (nat_lit 38846079155) (nat_lit 68719476736) (nat_lit 611739251499)

noncomputable def p129809 :=
@p129808 (nat_lit 429496729600000) true (nat_lit 11539536569) (nat_lit 1099511627776)
  (nat_lit 4880968540117) (nat_lit 3435973836800000) false (nat_lit 260155864003) (nat_lit 1099511627776)
  (nat_lit 210817892987) (nat_lit 3435973836800000)

noncomputable def p129810 :=
@p129809 false (nat_lit 58583701169) (nat_lit 1099511627776) (nat_lit 208341011737)
  (nat_lit 3435973836800000) false (nat_lit 60589490568517530943488) (nat_lit 881693130483) (nat_lit 1099511627776)
  (nat_lit 5104731904979) (nat_lit 3435973836800000)

noncomputable def p129811 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 17)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1)))))) }

noncomputable def p129812 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 17)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129813 :=
@p129811 false (nat_lit 260155864003) (nat_lit 1099511627776) (nat_lit 210817892987)
  (nat_lit 3435973836800000) false (nat_lit 58583701169) (nat_lit 1099511627776) (nat_lit 208341011737)
  (nat_lit 3435973836800000) p129812

noncomputable def p129814 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1)))))))
  false

noncomputable def p129815 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1)))))
  (nat_lit 254317) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129816 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1)))))
  false (nat_lit 1022959) (nat_lit 1048576)

noncomputable def p129817 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 144712489)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 144712489) (nat_lit 1048576)

noncomputable def p129818 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1))))
  false (nat_lit 155383852354927483521) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p129819 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3189913004350711) (nat_lit 1125899906842624)

noncomputable def p129820 :=
@p129819 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 155383852354927483521)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 17) (nat_lit 1) (nat_lit 3189913004350711) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32083 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3189913004350711)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32088 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129821 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 144712489)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 203900993762633814376448))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129822 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 144712489) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 21) (nat_lit 203900993762633814376448) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129823 :=
nat_lit 4538738830671894553743858972053651505363412540265520047881876441914314151174400

noncomputable def p129824 :=
nat_lit 4969541644193981420709258778272369092815541940514017599184234694293731942656

noncomputable def p129825 :=
nat_lit 11879127203383409766076577555451884392658664823267910763577663825032442448978176

noncomputable def p129826 :=
BSN.sin_dyadic_bound_f (nat_lit 2897607398) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129823 p31776 p129824
  p129825 p31779

noncomputable def p129827 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 2897607398)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129823 p31776 p129824 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129828 :=
p129826 p129824 (nat_lit 1022959) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129827 (Eq.refl true))

noncomputable def p129829 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 2897607398)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129825 p31779 p129824 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129830 :=
@BSN.sin_arg_round false (nat_lit 1022959) (nat_lit 1048576) (nat_lit 203900993762633814376448)
  (nat_lit 151115727451828646838272) (nat_lit 2897607398) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129828 (p129829 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129831 :=
p129821 (nat_lit 1022959) (nat_lit 1048576) (nat_lit 21) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129822 BSN.pi_near_15 p129830 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129832 :=
@p129817 (nat_lit 1) (nat_lit 4096) false (nat_lit 1022959) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129818 (nat_lit 250000000000000000) (nat_lit 144712489) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p129820 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 144712489) (nat_lit 1048576))
  (p129831 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129833 :=
@p129815 (nat_lit 1048576) (nat_lit 1022959) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 260155864003) (nat_lit 1099511627776) (nat_lit 210817892987) (nat_lit 3435973836800000)
  (@p32073 (nat_lit 254317) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32078
    (Eq.refl true))
  (@p129816 (nat_lit 204096) (nat_lit 819200000) (nat_lit 1022959) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p129832 (Eq.refl true)) (Eq.refl true))

noncomputable def p129834 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 17))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1))))))
  (nat_lit 254317) (nat_lit 1048576)

noncomputable def p129835 :=
@p129834 (nat_lit 1) (nat_lit 1048576) (nat_lit 230357) (nat_lit 1048576) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 58583701169) (nat_lit 1099511627776) (nat_lit 208341011737) (nat_lit 3435973836800000)
  (@p32073 (nat_lit 254317) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32078
    (Eq.refl true))

noncomputable def p129836 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1)))))
  true (nat_lit 230357) (nat_lit 1048576)

noncomputable def p129837 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1)))))
  true (nat_lit 230357) (nat_lit 1048576)

noncomputable def p129838 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 17) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 144712489)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 144712489) (nat_lit 1048576)

noncomputable def p129839 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 144712489)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 203900993762633814376448))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129840 :=
nat_lit 2523730257770694299378014655042371889243147207676628478867346572038749520404736

noncomputable def p129841 :=
nat_lit 7561251690023694935292625447570570929543810539148857401403671246727661097328896

noncomputable def p129842 :=
BSN.cos_dyadic_bound_f (nat_lit 2897607398) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129840 p31681 p129824
  p129841 p31684

noncomputable def p129843 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 2897607398)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129840 p31681 p129824 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129844 :=
p129842 p129824 (nat_lit 230357) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129843 (Eq.refl true))

noncomputable def p129845 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 2897607398)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129841 p31684 p129824 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129846 :=
@BSN.cos_arg_round false (nat_lit 230357) (nat_lit 1048576) (nat_lit 203900993762633814376448)
  (nat_lit 151115727451828646838272) (nat_lit 2897607398) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129844 (p129845 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129847 :=
p129839 (nat_lit 230357) (nat_lit 1048576) (nat_lit 21) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129822 BSN.pi_near_15 p129846 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129848 :=
@p129838 (nat_lit 1) (nat_lit 4096) true (nat_lit 230357) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129818 (nat_lit 250000000000000000) (nat_lit 144712489) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p129820 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 144712489) (nat_lit 1048576))
  (p129847 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129849 :=
p129835
  (@p129836 (nat_lit 3189) (nat_lit 12800000)
    (@p129837 (nat_lit 204096) (nat_lit 819200000) (nat_lit 230357) (nat_lit 1048576) (nat_lit 3189)
      (nat_lit 12800000) (p129848 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129850 :=
@p129814 (nat_lit 260155864003) (nat_lit 1099511627776) (nat_lit 210817892987)
  (nat_lit 3435973836800000) false (nat_lit 58583701169) (nat_lit 1099511627776) (nat_lit 208341011737)
  (nat_lit 3435973836800000) (p129833 (Eq.refl true)) p129849

noncomputable def p129851 :=
@p129810 false (nat_lit 51725605996708075929600) (nat_lit 5880520575) (nat_lit 137438953472)
  (nat_lit 2544654775927) (nat_lit 1717986918400000) d1197
  (p129813 p129850) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129852 :=
p129851 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129853 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 18)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1)))))) }

noncomputable def p129854 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 18)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129855 :=
@p129853 true (nat_lit 216945934837) (nat_lit 1099511627776) (nat_lit 205286372743)
  (nat_lit 3435973836800000) true (nat_lit 141762106335) (nat_lit 1099511627776) (nat_lit 204335741493)
  (nat_lit 3435973836800000) p129854

noncomputable def p129856 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1)))))))
  true

noncomputable def p129857 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1)))))
  (nat_lit 247151) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129858 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1)))))
  true (nat_lit 877787) (nat_lit 1048576)

noncomputable def p129859 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 147632031)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 147632031) (nat_lit 1048576)

noncomputable def p129860 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1))))
  false (nat_lit 6340747489593121449) (nat_lit 45035996273704960) (nat_lit 60888750048711)

noncomputable def p129861 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3254268794313975) (nat_lit 1125899906842624)

noncomputable def p129862 :=
@p129861 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 6340747489593121449)
  (nat_lit 45035996273704960) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 18) (nat_lit 1) (nat_lit 3254268794313975) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32137 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3254268794313975)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32142 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129863 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 147632031)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 149907278983451914534912))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129864 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 147632031) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 22) (nat_lit 149907278983451914534912) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129865 :=
nat_lit 1324988125247327707937541621647626458674097395342056532287901100376158318526720

noncomputable def p129866 :=
nat_lit 424173335906177175992049951054824730980919681794298864963795136975654256896

noncomputable def p129867 :=
nat_lit 3469520237865819710122907594870647199343905022601528719734561499334835013058816

noncomputable def p129868 :=
BSN.sin_dyadic_bound_f (nat_lit 2130310562) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129865 p31776 p129866
  p129867 p31779

noncomputable def p129869 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 2130310562)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129865 p31776 p129866 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129870 :=
p129868 p129866 (nat_lit 877787) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129869 (Eq.refl true))

noncomputable def p129871 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 2130310562)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129867 p31779 p129866 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129872 :=
@BSN.sin_arg_round false (nat_lit 877787) (nat_lit 1048576) (nat_lit 149907278983451914534912)
  (nat_lit 151115727451828646838272) (nat_lit 2130310562) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129870 (p129871 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129873 :=
p129863 (nat_lit 877787) (nat_lit 1048576) (nat_lit 22) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129864 BSN.pi_near_15 p129872 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129874 :=
@p129859 (nat_lit 257) (nat_lit 1048576) true (nat_lit 877787) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129860 (nat_lit 250000000000000000) (nat_lit 147632031) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p129862 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 147632031) (nat_lit 1048576))
  (p129873 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129875 :=
@p129857 (nat_lit 1048576) (nat_lit 877787) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 216945934837) (nat_lit 1099511627776) (nat_lit 205286372743) (nat_lit 3435973836800000)
  (@p32127 (nat_lit 247151) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32132
    (Eq.refl true))
  (@p129858 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 877787) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p129874 (Eq.refl true))
    (Eq.refl true))

noncomputable def p129876 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 18))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1))))))
  (nat_lit 247151) (nat_lit 1048576)

noncomputable def p129877 :=
@p129876 (nat_lit 1) (nat_lit 1048576) (nat_lit 573585) (nat_lit 1048576) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 141762106335) (nat_lit 1099511627776) (nat_lit 204335741493) (nat_lit 3435973836800000)
  (@p32127 (nat_lit 247151) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32132
    (Eq.refl true))

noncomputable def p129878 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1)))))
  false (nat_lit 573585) (nat_lit 1048576)

noncomputable def p129879 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1)))))
  false (nat_lit 573585) (nat_lit 1048576)

noncomputable def p129880 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 18) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 147632031)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 147632031) (nat_lit 1048576)

noncomputable def p129881 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 147632031)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 149907278983451914534912))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129882 :=
nat_lit 736293035508918138710186256449150176921601183937495539655484520269854912184576

noncomputable def p129883 :=
nat_lit 2208030759854942061778574669445340881302841712448898021236525970535613428039936

noncomputable def p129884 :=
BSN.cos_dyadic_bound_f (nat_lit 2130310562) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129882 p31681 p129866
  p129883 p31684

noncomputable def p129885 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 2130310562)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129882 p31681 p129866 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129886 :=
p129884 p129866 (nat_lit 573585) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129885 (Eq.refl true))

noncomputable def p129887 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 2130310562)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129883 p31684 p129866 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129888 :=
@BSN.cos_arg_round false (nat_lit 573585) (nat_lit 1048576) (nat_lit 149907278983451914534912)
  (nat_lit 151115727451828646838272) (nat_lit 2130310562) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129886 (p129887 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129889 :=
p129881 (nat_lit 573585) (nat_lit 1048576) (nat_lit 22) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129864 BSN.pi_near_15 p129888 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129890 :=
@p129880 (nat_lit 257) (nat_lit 1048576) false (nat_lit 573585) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129860 (nat_lit 250000000000000000) (nat_lit 147632031) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p129862 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 147632031) (nat_lit 1048576))
  (p129889 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129891 :=
p129877
  (@p129878 (nat_lit 819509) (nat_lit 3276800000)
    (@p129879 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 573585) (nat_lit 1048576)
      (nat_lit 819509) (nat_lit 3276800000) (p129890 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129892 :=
@p129856 (nat_lit 216945934837) (nat_lit 1099511627776) (nat_lit 205286372743)
  (nat_lit 3435973836800000) true (nat_lit 141762106335) (nat_lit 1099511627776) (nat_lit 204335741493)
  (nat_lit 3435973836800000) (p129875 (Eq.refl true)) p129891

noncomputable def p129893 :=
@p129806 true (nat_lit 13017934787080271953920) (nat_lit 94717941735) (nat_lit 1099511627776)
  (nat_lit 5293645293347) (nat_lit 3435973836800000)
  (@p129807 (nat_lit 5104731904979) (nat_lit 3435973836800000) false (nat_lit 5880520575)
    (nat_lit 137438953472) (nat_lit 2544654775927) (nat_lit 1717986918400000)
    (p129097 (nat_lit 17) (nat_lit 18) (Eq.refl true) (Eq.refl true))
    (p129852 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (p129855 p129892)

noncomputable def p129894 :=
p129893 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129895 :=
p129894 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129896 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 19)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1)))))) }

noncomputable def p129897 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 19)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129898 :=
@p129896 false (nat_lit 58698561031) (nat_lit 549755813888) (nat_lit 19791439129)
  (nat_lit 343597383680000) false (nat_lit 223260161751) (nat_lit 1099511627776) (nat_lit 39857922633)
  (nat_lit 687194767360000) p129897

noncomputable def p129899 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1)))))))
  false

noncomputable def p129900 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1)))))
  (nat_lit 240559) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129901 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1)))))
  false (nat_lit 488018) (nat_lit 1048576)

noncomputable def p129902 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 150393653)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 150393653) (nat_lit 1048576)

noncomputable def p129903 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1))))
  false (nat_lit 161483955675568691841) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p129904 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3315143513283831) (nat_lit 1125899906842624)

noncomputable def p129905 :=
@p129904 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 161483955675568691841)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 19) (nat_lit 1) (nat_lit 3315143513283831) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32192 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3315143513283831)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32197 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129906 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 150393653)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 73154893703330855387136))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129907 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 150393653) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 22) (nat_lit 73154893703330855387136) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129908 :=
nat_lit 1168030899828743029369131328856478736

noncomputable def p129909 :=
BSN.sin_dyadic_bound_f (nat_lit 1039593566) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129908 p31525 p129908
  p129908 p31526

noncomputable def p129910 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1039593566)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129908 p31525 p129908 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129911 :=
p129909 p129908 (nat_lit 488018) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129910 (Eq.refl true))

noncomputable def p129912 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1039593566)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129908 p31526 p129908 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129913 :=
@BSN.sin_arg_round false (nat_lit 488018) (nat_lit 1048576) (nat_lit 73154893703330855387136)
  (nat_lit 151115727451828646838272) (nat_lit 1039593566) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129911 (p129912 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129914 :=
p129906 (nat_lit 488018) (nat_lit 1048576) (nat_lit 22) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129907 BSN.pi_near_15 p129913 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129915 :=
@p129902 (nat_lit 1) (nat_lit 4096) false (nat_lit 488018) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129903 (nat_lit 250000000000000000) (nat_lit 150393653) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p129905 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 150393653) (nat_lit 1048576))
  (p129914 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129916 :=
@p129900 (nat_lit 1048576) (nat_lit 244009) (nat_lit 524288) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 58698561031) (nat_lit 549755813888) (nat_lit 19791439129) (nat_lit 343597383680000)
  (@p32182 (nat_lit 240559) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32187
    (Eq.refl true))
  (@p129901 (nat_lit 204096) (nat_lit 819200000) (nat_lit 244009) (nat_lit 524288) (nat_lit 3189)
    (nat_lit 12800000) (p129915 (Eq.refl true)) (Eq.refl true))

noncomputable def p129917 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 19))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1))))))
  (nat_lit 240559) (nat_lit 1048576)

noncomputable def p129918 :=
@p129917 (nat_lit 1) (nat_lit 1048576) (nat_lit 928089) (nat_lit 1048576) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 223260161751) (nat_lit 1099511627776) (nat_lit 39857922633) (nat_lit 687194767360000)
  (@p32182 (nat_lit 240559) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32187
    (Eq.refl true))

noncomputable def p129919 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1)))))
  true (nat_lit 928089) (nat_lit 1048576)

noncomputable def p129920 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1)))))
  true (nat_lit 928089) (nat_lit 1048576)

noncomputable def p129921 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 19) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 150393653)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 150393653) (nat_lit 1048576)

noncomputable def p129922 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 150393653)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 73154893703330855387136))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129923 :=
BSN.cos_dyadic_bound_f (nat_lit 1039593566) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p129908 p31541 p129908
  p129908 p31542

noncomputable def p129924 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 1039593566)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129908 p31541 p129908 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129925 :=
p129923 p129908 (nat_lit 928089) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129924 (Eq.refl true))

noncomputable def p129926 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 1039593566)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p129908 p31542 p129908 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129927 :=
@BSN.cos_arg_round false (nat_lit 928089) (nat_lit 1048576) (nat_lit 73154893703330855387136)
  (nat_lit 151115727451828646838272) (nat_lit 1039593566) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129925 (p129926 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129928 :=
p129922 (nat_lit 928089) (nat_lit 1048576) (nat_lit 22) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129907 BSN.pi_near_15 p129927 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129929 :=
@p129921 (nat_lit 1) (nat_lit 4096) true (nat_lit 928089) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129903 (nat_lit 250000000000000000) (nat_lit 150393653) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p129905 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 150393653) (nat_lit 1048576))
  (p129928 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129930 :=
p129918
  (@p129919 (nat_lit 3189) (nat_lit 12800000)
    (@p129920 (nat_lit 204096) (nat_lit 819200000) (nat_lit 928089) (nat_lit 1048576) (nat_lit 3189)
      (nat_lit 12800000) (p129929 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129931 :=
@p129899 (nat_lit 58698561031) (nat_lit 549755813888) (nat_lit 19791439129) (nat_lit 343597383680000)
  false (nat_lit 223260161751) (nat_lit 1099511627776) (nat_lit 39857922633) (nat_lit 687194767360000)
  (p129916 (Eq.refl true)) p129930

noncomputable def p129932 :=
@p129802 false (nat_lit 141333665567732888764416) (nat_lit 8033888751) (nat_lit 68719476736)
  (nat_lit 343308431657) (nat_lit 214748364800000)
  (@p129803 (nat_lit 2655009138861) (nat_lit 1717986918400000) true (nat_lit 94717941735)
    (nat_lit 1099511627776) (nat_lit 5293645293347) (nat_lit 3435973836800000)
    (p129097 (nat_lit 18) (nat_lit 19) (Eq.refl true) (Eq.refl true))
    p129895)
  (p129898 p129931)

noncomputable def p129933 :=
p129932 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129934 :=
p129933 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129935 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 20)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1)))))) }

noncomputable def p129936 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 20)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129937 :=
@p129935 false (nat_lit 38924433159) (nat_lit 1099511627776) (nat_lit 38533811921)
  (nat_lit 687194767360000) true (nat_lit 242757713619) (nat_lit 1099511627776) (nat_lit 39077149421)
  (nat_lit 687194767360000) p129936

noncomputable def p129938 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1)))))))
  false

noncomputable def p129939 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1)))))
  (nat_lit 234469) (nat_lit 1048576) (nat_lit 1)

noncomputable def p129940 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1)))))
  false (nat_lit 166011) (nat_lit 1048576)

noncomputable def p129941 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 153013525)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 153013525) (nat_lit 1048576)

noncomputable def p129942 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1))))
  false (nat_lit 164297022270761753217) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p129943 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3372893643545847) (nat_lit 1125899906842624)

noncomputable def p129944 :=
@p129943 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 164297022270761753217)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 20) (nat_lit 1) (nat_lit 3372893643545847) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32247 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3372893643545847)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32252 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129945 :=
BSN.cos_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 153013525)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 213346210115728378429440))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129946 :=
BSN.sin_reduce_arg_pos_rat_q0 (nat_lit 153013525) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 23) (nat_lit 213346210115728378429440) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129947 :=
nat_lit 3026042839892554007350998500149082680486736086653689149945762452553823797190625

noncomputable def p129948 :=
nat_lit 7139060364043418775003065945701861582814721889091605631740092053105000390625

noncomputable def p129949 :=
nat_lit 9063850398949575184502989368555844318294578816182884238573807173555261390790625

noncomputable def p129950 :=
BSN.cos_dyadic_bound_f (nat_lit 3031831995) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129947 p31681 p129948
  p129949 p31684

noncomputable def p129951 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 3031831995)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129947 p31681 p129948 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129952 :=
p129950 p129948 (nat_lit 166011) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129951 (Eq.refl true))

noncomputable def p129953 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 3031831995)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129949 p31684 p129948 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129954 :=
@BSN.cos_arg_round false (nat_lit 166011) (nat_lit 1048576) (nat_lit 213346210115728378429440)
  (nat_lit 151115727451828646838272) (nat_lit 3031831995) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129952 (p129953 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129955 :=
p129945 (nat_lit 166011) (nat_lit 1048576) (nat_lit 23) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129946 BSN.pi_near_15 p129954 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129956 :=
@p129941 (nat_lit 257) (nat_lit 1048576) false (nat_lit 166011) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129942 (nat_lit 250000000000000000) (nat_lit 153013525) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p129944 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 153013525) (nat_lit 1048576))
  (p129955 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129957 :=
@p129939 (nat_lit 1048576) (nat_lit 166011) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 38924433159) (nat_lit 1099511627776) (nat_lit 38533811921) (nat_lit 687194767360000)
  (@p32237 (nat_lit 234469) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32242
    (Eq.refl true))
  (@p129940 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 166011) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p129956 (Eq.refl true))
    (Eq.refl true))

noncomputable def p129958 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 20))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1))))))
  (nat_lit 234469) (nat_lit 1048576)

noncomputable def p129959 :=
@p129958 (nat_lit 1) (nat_lit 1048576) (nat_lit 1035351) (nat_lit 1048576) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 242757713619) (nat_lit 1099511627776) (nat_lit 39077149421) (nat_lit 687194767360000)
  (@p32237 (nat_lit 234469) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32242
    (Eq.refl true))

noncomputable def p129960 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1)))))
  false (nat_lit 1035351) (nat_lit 1048576)

noncomputable def p129961 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1)))))
  false (nat_lit 1035351) (nat_lit 1048576)

noncomputable def p129962 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 20) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 153013525)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 153013525) (nat_lit 1048576)

noncomputable def p129963 :=
BSN.sin_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 153013525)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 213346210115728378429440))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129964 :=
nat_lit 5441165863515362478211794847511787335609873178465367185396980340954398834630625

noncomputable def p129965 :=
nat_lit 14239114020998450479204695827190211436415586870065051457397845505842207899590625

noncomputable def p129966 :=
BSN.sin_dyadic_bound_f (nat_lit 3031831995) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129964 p31776 p129948
  p129965 p31779

noncomputable def p129967 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 3031831995)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129964 p31776 p129948 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129968 :=
p129966 p129948 (nat_lit 1035351) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129967 (Eq.refl true))

noncomputable def p129969 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 3031831995)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129965 p31779 p129948 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129970 :=
@BSN.sin_arg_round false (nat_lit 1035351) (nat_lit 1048576) (nat_lit 213346210115728378429440)
  (nat_lit 151115727451828646838272) (nat_lit 3031831995) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129968 (p129969 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129971 :=
p129963 (nat_lit 1035351) (nat_lit 1048576) (nat_lit 23) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129946 BSN.pi_near_15 p129970 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129972 :=
@p129962 (nat_lit 257) (nat_lit 1048576) false (nat_lit 1035351) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129942 (nat_lit 250000000000000000) (nat_lit 153013525) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p129944 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 153013525) (nat_lit 1048576))
  (p129971 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p129973 :=
p129959
  (@p129960 (nat_lit 819509) (nat_lit 3276800000)
    (@p129961 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 1035351) (nat_lit 1048576)
      (nat_lit 819509) (nat_lit 3276800000) (p129972 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129974 :=
@p129938 (nat_lit 38924433159) (nat_lit 1099511627776) (nat_lit 38533811921) (nat_lit 687194767360000)
  true (nat_lit 242757713619) (nat_lit 1099511627776) (nat_lit 39077149421) (nat_lit 687194767360000)
  (p129957 (Eq.refl true)) p129973

noncomputable def p129975 :=
@p129798 true (nat_lit 7848828955542115319808) (nat_lit 114215493603) (nat_lit 1099511627776)
  (nat_lit 5688320653617) (nat_lit 3435973836800000)
  (@p129799 (nat_lit 1376983167253) (nat_lit 858993459200000) false (nat_lit 8033888751)
    (nat_lit 68719476736) (nat_lit 343308431657) (nat_lit 214748364800000)
    (p129097 (nat_lit 19) (nat_lit 20) (Eq.refl true) (Eq.refl true))
    p129934)
  (p129937 p129974)

noncomputable def p129976 :=
p129975 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129977 :=
p129976 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p129978 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 21)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1)))))) }

noncomputable def p129979 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 21)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p129980 :=
@p129978 true (nat_lit 47866780647) (nat_lit 274877906944) (nat_lit 9601738719)
  (nat_lit 171798691840000) false (nat_lit 9037281319) (nat_lit 68719476736) (nat_lit 2384431711)
  (nat_lit 42949672960000) p129979

noncomputable def p129981 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1)))))))
  true

noncomputable def p129982 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1)))))
  (nat_lit 114409) (nat_lit 524288) (nat_lit 1)

noncomputable def p129983 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1)))))
  true (nat_lit 836766) (nat_lit 1048576)

noncomputable def p129984 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38876395)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  false (nat_lit 38876395) (nat_lit 262144)

noncomputable def p129985 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1))))
  false (nat_lit 166972845694272035457) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p129986 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3427826275261687) (nat_lit 1125899906842624)

noncomputable def p129987 :=
@p129986 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 166972845694272035457)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 21) (nat_lit 1) (nat_lit 3427826275261687) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32302 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3427826275261687)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32307 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p129988 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38876395)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24436281482890769858560))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37778931862957161709568)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p129989 :=
BSN.sin_reduce_arg_pos_rat_q2 (nat_lit 38876395) (nat_lit 262144) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 23) (nat_lit 24436281482890769858560) (nat_lit 37778931862957161709568)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p129990 :=
nat_lit 133025601193854991839773116401656889427147207272764156927575489646031272358721

noncomputable def p129991 :=
nat_lit 13858699488852093391808515851740595328361562185338389980562779762871186241

noncomputable def p129992 :=
nat_lit 399049086182587271332535732173267187090784898693921794002765343378568074703681

noncomputable def p129993 :=
BSN.cos_dyadic_bound_f (nat_lit 1389041783) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p129990 p31681 p129991
  p129992 p31684

noncomputable def p129994 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1389041783)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p129990 p31681 p129991 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129995 :=
p129993 p129991 (nat_lit 836766) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p129994 (Eq.refl true))

noncomputable def p129996 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1389041783)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p129992 p31684 p129991 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p129997 :=
@BSN.cos_arg_round false (nat_lit 836766) (nat_lit 1048576) (nat_lit 24436281482890769858560)
  (nat_lit 37778931862957161709568) (nat_lit 1389041783) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p129995 (p129996 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p129998 :=
p129988 (nat_lit 836766) (nat_lit 1048576) (nat_lit 23) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129989 BSN.pi_near_15 p129997 (Eq.refl true)
  (Eq.refl true)

noncomputable def p129999 :=
@p129984 (nat_lit 1) (nat_lit 4096) true (nat_lit 836766) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129985 (nat_lit 250000000000000000) (nat_lit 38876395) (nat_lit 262144) (nat_lit 1)
    (nat_lit 4096) p129987 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 38876395) (nat_lit 262144))
  (p129998 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130000 :=
@p129982 (nat_lit 524288) (nat_lit 418383) (nat_lit 524288) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 47866780647) (nat_lit 274877906944) (nat_lit 9601738719) (nat_lit 171798691840000)
  (@p32292 (nat_lit 114409) (nat_lit 524288) (nat_lit 1) (nat_lit 524288) p32297
    (Eq.refl true))
  (@p129983 (nat_lit 204096) (nat_lit 819200000) (nat_lit 418383) (nat_lit 524288) (nat_lit 3189)
    (nat_lit 12800000) (p129999 (Eq.refl true)) (Eq.refl true))

noncomputable def p130001 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 21))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1))))))
  (nat_lit 114409) (nat_lit 524288)

noncomputable def p130002 :=
@p130001 (nat_lit 1) (nat_lit 524288) (nat_lit 78991) (nat_lit 131072) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 9037281319) (nat_lit 68719476736) (nat_lit 2384431711) (nat_lit 42949672960000)
  (@p32292 (nat_lit 114409) (nat_lit 524288) (nat_lit 1) (nat_lit 524288) p32297
    (Eq.refl true))

noncomputable def p130003 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1)))))
  true (nat_lit 78991) (nat_lit 131072)

noncomputable def p130004 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1)))))
  true (nat_lit 631928) (nat_lit 1048576)

noncomputable def p130005 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 21) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38876395)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  false (nat_lit 38876395) (nat_lit 262144)

noncomputable def p130006 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38876395)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24436281482890769858560))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37778931862957161709568)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130007 :=
nat_lit 3722727426075147580225078328488789921

noncomputable def p130008 :=
BSN.sin_dyadic_bound_f (nat_lit 1389041783) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130007 p31525 p130007
  p130007 p31526

noncomputable def p130009 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1389041783)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130007 p31525 p130007 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130010 :=
p130008 p130007 (nat_lit 631928) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130009 (Eq.refl true))

noncomputable def p130011 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1389041783)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130007 p31526 p130007 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130012 :=
@BSN.sin_arg_round false (nat_lit 631928) (nat_lit 1048576) (nat_lit 24436281482890769858560)
  (nat_lit 37778931862957161709568) (nat_lit 1389041783) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130010 (p130011 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130013 :=
p130006 (nat_lit 631928) (nat_lit 1048576) (nat_lit 23) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p129989 BSN.pi_near_15 p130012 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130014 :=
@p130005 (nat_lit 1) (nat_lit 4096) true (nat_lit 631928) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p129985 (nat_lit 250000000000000000) (nat_lit 38876395) (nat_lit 262144) (nat_lit 1)
    (nat_lit 4096) p129987 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 38876395) (nat_lit 262144))
  (p130013 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130015 :=
p130002
  (@p130003 (nat_lit 3189) (nat_lit 12800000)
    (@p130004 (nat_lit 204096) (nat_lit 819200000) (nat_lit 78991) (nat_lit 131072) (nat_lit 3189)
      (nat_lit 12800000) (p130014 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130016 :=
@p129981 (nat_lit 47866780647) (nat_lit 274877906944) (nat_lit 9601738719) (nat_lit 171798691840000)
  false (nat_lit 9037281319) (nat_lit 68719476736) (nat_lit 2384431711) (nat_lit 42949672960000)
  (p130000 (Eq.refl true)) p130015

noncomputable def p130017 :=
@p129794 false (nat_lit 2087766938181210996736) (nat_lit 30381007501) (nat_lit 1099511627776)
  (nat_lit 5879075190497) (nat_lit 3435973836800000)
  (@p129795 (nat_lit 5700601728617) (nat_lit 3435973836800000) true (nat_lit 114215493603)
    (nat_lit 1099511627776) (nat_lit 5688320653617) (nat_lit 3435973836800000)
    (p129097 (nat_lit 20) (nat_lit 21) (Eq.refl true) (Eq.refl true))
    p129977)
  (p129980 p130016)

noncomputable def p130018 :=
p130017 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130019 :=
p130018 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130020 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 22)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1)))))) }

noncomputable def p130021 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 22)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130022 :=
@p130020 false (nat_lit 228311386719) (nat_lit 1099511627776) (nat_lit 185700633647)
  (nat_lit 3435973836800000) false (nat_lit 26574891261) (nat_lit 549755813888) (nat_lit 91626065261)
  (nat_lit 1717986918400000) p130021

noncomputable def p130023 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1)))))))
  false

noncomputable def p130024 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1)))))
  (nat_lit 223557) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130025 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1)))))
  false (nat_lit 1021267) (nat_lit 1048576)

noncomputable def p130026 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 157881703)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 157881703) (nat_lit 1048576)

noncomputable def p130027 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1))))
  false (nat_lit 169524187887368821377) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p130028 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3480203401436407) (nat_lit 1125899906842624)

noncomputable def p130029 :=
@p130028 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 169524187887368821377)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 22) (nat_lit 1) (nat_lit 3480203401436407) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32357 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3480203401436407)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32362 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130030 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 157881703)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 202808509365658809532416))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130031 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 157881703) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 23) (nat_lit 202808509365658809532416) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130032 :=
nat_lit 4442141678808729687932929622240588275222904597404700059999015687020489729801825

noncomputable def p130033 :=
nat_lit 4760482566317120981259289747005145933637757315907162960217318792841763126881

noncomputable def p130034 :=
nat_lit 11626473139391683367759443493896865722643622338500840940918974949865253104418401

noncomputable def p130035 :=
BSN.sin_dyadic_bound_f (nat_lit 2882082261) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130032 p31776 p130033
  p130034 p31779

noncomputable def p130036 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 2882082261)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130032 p31776 p130033 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130037 :=
p130035 p130033 (nat_lit 1021267) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130036 (Eq.refl true))

noncomputable def p130038 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 2882082261)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130034 p31779 p130033 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130039 :=
@BSN.sin_arg_round false (nat_lit 1021267) (nat_lit 1048576) (nat_lit 202808509365658809532416)
  (nat_lit 151115727451828646838272) (nat_lit 2882082261) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130037 (p130038 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130040 :=
p130030 (nat_lit 1021267) (nat_lit 1048576) (nat_lit 23) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130031 BSN.pi_near_15 p130039 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130041 :=
@p130026 (nat_lit 1) (nat_lit 4096) false (nat_lit 1021267) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130027 (nat_lit 250000000000000000) (nat_lit 157881703) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130029 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 157881703) (nat_lit 1048576))
  (p130040 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130042 :=
@p130024 (nat_lit 1048576) (nat_lit 1021267) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 228311386719) (nat_lit 1099511627776) (nat_lit 185700633647) (nat_lit 3435973836800000)
  (@p32347 (nat_lit 223557) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32352
    (Eq.refl true))
  (@p130025 (nat_lit 204096) (nat_lit 819200000) (nat_lit 1021267) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p130041 (Eq.refl true)) (Eq.refl true))

noncomputable def p130043 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 22))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1))))))
  (nat_lit 223557) (nat_lit 1048576)

noncomputable def p130044 :=
@p130043 (nat_lit 1) (nat_lit 1048576) (nat_lit 118873) (nat_lit 524288) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 26574891261) (nat_lit 549755813888) (nat_lit 91626065261) (nat_lit 1717986918400000)
  (@p32347 (nat_lit 223557) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32352
    (Eq.refl true))

noncomputable def p130045 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1)))))
  true (nat_lit 118873) (nat_lit 524288)

noncomputable def p130046 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1)))))
  true (nat_lit 237746) (nat_lit 1048576)

noncomputable def p130047 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 22) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 157881703)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 157881703) (nat_lit 1048576)

noncomputable def p130048 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 157881703)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 202808509365658809532416))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130049 :=
nat_lit 2469972258256546324843298363354551328872119335143014327981771967808201744612961

noncomputable def p130050 :=
nat_lit 7400395809637004732567376510569643694749082490797228658024881265838921707585121

noncomputable def p130051 :=
BSN.cos_dyadic_bound_f (nat_lit 2882082261) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130049 p31681 p130033
  p130050 p31684

noncomputable def p130052 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 2882082261)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130049 p31681 p130033 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130053 :=
p130051 p130033 (nat_lit 237746) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130052 (Eq.refl true))

noncomputable def p130054 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 2882082261)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130050 p31684 p130033 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130055 :=
@BSN.cos_arg_round false (nat_lit 237746) (nat_lit 1048576) (nat_lit 202808509365658809532416)
  (nat_lit 151115727451828646838272) (nat_lit 2882082261) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130053 (p130054 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130056 :=
p130048 (nat_lit 237746) (nat_lit 1048576) (nat_lit 23) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130031 BSN.pi_near_15 p130055 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130057 :=
@p130047 (nat_lit 1) (nat_lit 4096) true (nat_lit 237746) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130027 (nat_lit 250000000000000000) (nat_lit 157881703) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130029 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 157881703) (nat_lit 1048576))
  (p130056 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130058 :=
p130044
  (@p130045 (nat_lit 3189) (nat_lit 12800000)
    (@p130046 (nat_lit 204096) (nat_lit 819200000) (nat_lit 118873) (nat_lit 524288) (nat_lit 3189)
      (nat_lit 12800000) (p130057 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130059 :=
@p130023 (nat_lit 228311386719) (nat_lit 1099511627776) (nat_lit 185700633647)
  (nat_lit 3435973836800000) false (nat_lit 26574891261) (nat_lit 549755813888) (nat_lit 91626065261)
  (nat_lit 1717986918400000) (p130042 (Eq.refl true)) p130058

noncomputable def p130060 :=
@p129790 false (nat_lit 45921537453801995239424) (nat_lit 83530790023) (nat_lit 1099511627776)
  (nat_lit 6062327321019) (nat_lit 3435973836800000)
  (@p129791 (nat_lit 5892636502997) (nat_lit 3435973836800000) false (nat_lit 30381007501)
    (nat_lit 1099511627776) (nat_lit 5879075190497) (nat_lit 3435973836800000)
    (p129097 (nat_lit 21) (nat_lit 22) (Eq.refl true) (Eq.refl true))
    p130019)
  (p130022 p130059)

noncomputable def p130061 :=
p130060 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130062 :=
p130061 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130063 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 23)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1)))))) }

noncomputable def p130064 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 23)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130065 :=
@p130063 true (nat_lit 81990031785) (nat_lit 1099511627776) (nat_lit 180352585171)
  (nat_lit 3435973836800000) true (nat_lit 214101566247) (nat_lit 1099511627776) (nat_lit 182240816421)
  (nat_lit 3435973836800000) p130064

noncomputable def p130066 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1)))))))
  true

noncomputable def p130067 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1)))))
  (nat_lit 218643) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130068 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1)))))
  true (nat_lit 374995) (nat_lit 1048576)

noncomputable def p130069 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 80076061)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 80076061) (nat_lit 524288)

noncomputable def p130070 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1))))
  false (nat_lit 171962032488029772417) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p130071 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3530250507853047) (nat_lit 1125899906842624)

noncomputable def p130072 :=
@p130071 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 171962032488029772417)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 23) (nat_lit 1) (nat_lit 3530250507853047) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32412 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3530250507853047)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32417 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130073 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 80076061)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27633155678556559245312))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130074 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 80076061) (nat_lit 524288) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 24) (nat_lit 27633155678556559245312) (nat_lit 75557863725914323419136)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130075 :=
nat_lit 380472011702905303742576134465980481

noncomputable def p130076 :=
BSN.sin_dyadic_bound_f (nat_lit 785381521) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130075 p31525 p130075
  p130075 p31526

noncomputable def p130077 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 785381521)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130075 p31525 p130075 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130078 :=
p130076 p130075 (nat_lit 374995) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130077 (Eq.refl true))

noncomputable def p130079 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 785381521)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130075 p31526 p130075 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130080 :=
@BSN.sin_arg_round false (nat_lit 374995) (nat_lit 1048576) (nat_lit 27633155678556559245312)
  (nat_lit 75557863725914323419136) (nat_lit 785381521) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130078 (p130079 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130081 :=
p130073 (nat_lit 374995) (nat_lit 1048576) (nat_lit 24) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130074 BSN.pi_near_15 p130080 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130082 :=
@p130069 (nat_lit 257) (nat_lit 1048576) true (nat_lit 374995) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130070 (nat_lit 250000000000000000) (nat_lit 80076061) (nat_lit 524288) (nat_lit 257)
    (nat_lit 1048576) p130072 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 80076061) (nat_lit 524288))
  (p130081 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130083 :=
@p130067 (nat_lit 1048576) (nat_lit 374995) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 81990031785) (nat_lit 1099511627776) (nat_lit 180352585171) (nat_lit 3435973836800000)
  (@p32402 (nat_lit 218643) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32407
    (Eq.refl true))
  (@p130068 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 374995) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p130082 (Eq.refl true))
    (Eq.refl true))

noncomputable def p130084 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1))))))
  (nat_lit 218643) (nat_lit 1048576)

noncomputable def p130085 :=
@p130084 (nat_lit 1) (nat_lit 1048576) (nat_lit 979229) (nat_lit 1048576) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 214101566247) (nat_lit 1099511627776) (nat_lit 182240816421) (nat_lit 3435973836800000)
  (@p32402 (nat_lit 218643) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32407
    (Eq.refl true))

noncomputable def p130086 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1)))))
  false (nat_lit 979229) (nat_lit 1048576)

noncomputable def p130087 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1)))))
  false (nat_lit 979229) (nat_lit 1048576)

noncomputable def p130088 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 23) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 80076061)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 80076061) (nat_lit 524288)

noncomputable def p130089 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 80076061)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27633155678556559245312))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130090 :=
BSN.cos_dyadic_bound_f (nat_lit 785381521) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130075 p31541 p130075
  p130075 p31542

noncomputable def p130091 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 785381521)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130075 p31541 p130075 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130092 :=
p130090 p130075 (nat_lit 979229) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130091 (Eq.refl true))

noncomputable def p130093 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 785381521)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130075 p31542 p130075 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130094 :=
@BSN.cos_arg_round false (nat_lit 979229) (nat_lit 1048576) (nat_lit 27633155678556559245312)
  (nat_lit 75557863725914323419136) (nat_lit 785381521) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130092 (p130093 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130095 :=
p130089 (nat_lit 979229) (nat_lit 1048576) (nat_lit 24) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130074 BSN.pi_near_15 p130094 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130096 :=
@p130088 (nat_lit 257) (nat_lit 1048576) false (nat_lit 979229) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130070 (nat_lit 250000000000000000) (nat_lit 80076061) (nat_lit 524288) (nat_lit 257)
    (nat_lit 1048576) p130072 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 80076061) (nat_lit 524288))
  (p130095 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130097 :=
p130085
  (@p130086 (nat_lit 819509) (nat_lit 3276800000)
    (@p130087 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 979229) (nat_lit 1048576)
      (nat_lit 819509) (nat_lit 3276800000) (p130096 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130098 :=
@p130066 (nat_lit 81990031785) (nat_lit 1099511627776) (nat_lit 180352585171)
  (nat_lit 3435973836800000) true (nat_lit 214101566247) (nat_lit 1099511627776) (nat_lit 182240816421)
  (nat_lit 3435973836800000) (p130083 (Eq.refl true)) p130097

noncomputable def p130099 :=
@p129786 true (nat_lit 143564086706026078797824) (nat_lit 4080336757) (nat_lit 34359738368)
  (nat_lit 39028550859) (nat_lit 21474836480000)
  (@p129787 (nat_lit 1519584284161) (nat_lit 858993459200000) false (nat_lit 83530790023)
    (nat_lit 1099511627776) (nat_lit 6062327321019) (nat_lit 3435973836800000)
    (p129097 (nat_lit 22) (nat_lit 23) (Eq.refl true) (Eq.refl true))
    p130062)
  (p130065 p130098)

noncomputable def p130100 :=
p130099 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130101 :=
p130100 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130102 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 24)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1)))))) }

noncomputable def p130103 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 24)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130104 :=
@p130102 true (nat_lit 145048879325) (nat_lit 1099511627776) (nat_lit 35371313147)
  (nat_lit 687194767360000) false (nat_lit 85633365237) (nat_lit 549755813888) (nat_lit 17723935011)
  (nat_lit 343597383680000) p130103

noncomputable def p130105 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1)))))))
  true

noncomputable def p130106 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1)))))
  (nat_lit 214039) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130107 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1)))))
  true (nat_lit 677675) (nat_lit 1048576)

noncomputable def p130108 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 162325997)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 162325997) (nat_lit 1048576)

noncomputable def p130109 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1))))
  false (nat_lit 174296212467396795009) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p130110 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3578169457974519) (nat_lit 1125899906842624)

noncomputable def p130111 :=
@p130110 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 174296212467396795009)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 24) (nat_lit 1) (nat_lit 3578169457974519) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32467 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3578169457974519)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32472 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130112 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 162325997)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 131182686233243150188544))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130113 :=
BSN.sin_reduce_arg_pos_rat_q2 (nat_lit 162325997) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 24) (nat_lit 131182686233243150188544) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130114 :=
nat_lit 431680470474422155765916766512963097715255405965538874649770243098071795690625

noncomputable def p130115 :=
nat_lit 145872609826803161040088229540867375722704804178158916288086275393062890625

noncomputable def p130116 :=
nat_lit 1294749666203612860975670123079807558394320808288260306116734556743429261290625

noncomputable def p130117 :=
BSN.cos_dyadic_bound_f (nat_lit 1864218095) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130114 p31681 p130115
  p130116 p31684

noncomputable def p130118 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1864218095)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130114 p31681 p130115 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130119 :=
p130117 p130115 (nat_lit 677675) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130118 (Eq.refl true))

noncomputable def p130120 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1864218095)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130116 p31684 p130115 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130121 :=
@BSN.cos_arg_round false (nat_lit 677675) (nat_lit 1048576) (nat_lit 131182686233243150188544)
  (nat_lit 151115727451828646838272) (nat_lit 1864218095) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130119 (p130120 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130122 :=
p130112 (nat_lit 677675) (nat_lit 1048576) (nat_lit 24) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130113 BSN.pi_near_15 p130121 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130123 :=
@p130108 (nat_lit 1) (nat_lit 4096) true (nat_lit 677675) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130109 (nat_lit 250000000000000000) (nat_lit 162325997) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130111 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 162325997) (nat_lit 1048576))
  (p130122 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130124 :=
@p130106 (nat_lit 1048576) (nat_lit 677675) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 145048879325) (nat_lit 1099511627776) (nat_lit 35371313147) (nat_lit 687194767360000)
  (@p32457 (nat_lit 214039) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32462
    (Eq.refl true))
  (@p130107 (nat_lit 204096) (nat_lit 819200000) (nat_lit 677675) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p130123 (Eq.refl true)) (Eq.refl true))

noncomputable def p130125 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 24))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1))))))
  (nat_lit 214039) (nat_lit 1048576)

noncomputable def p130126 :=
@p130125 (nat_lit 1) (nat_lit 1048576) (nat_lit 400083) (nat_lit 524288) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 85633365237) (nat_lit 549755813888) (nat_lit 17723935011) (nat_lit 343597383680000)
  (@p32457 (nat_lit 214039) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32462
    (Eq.refl true))

noncomputable def p130127 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1)))))
  true (nat_lit 400083) (nat_lit 524288)

noncomputable def p130128 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1)))))
  true (nat_lit 800166) (nat_lit 1048576)

noncomputable def p130129 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 24) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 162325997)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 162325997) (nat_lit 1048576)

noncomputable def p130130 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 162325997)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 131182686233243150188544))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130131 :=
nat_lit 776908148766098437849818109139700881986881566894627447236555968556214781930625

noncomputable def p130132 :=
nat_lit 2034523262542919179726887285851388524690662581707735818802703968439449946090625

noncomputable def p130133 :=
BSN.sin_dyadic_bound_f (nat_lit 1864218095) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130131 p31776 p130115
  p130132 p31779

noncomputable def p130134 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 1864218095)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130131 p31776 p130115 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130135 :=
p130133 p130115 (nat_lit 800166) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130134 (Eq.refl true))

noncomputable def p130136 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 1864218095)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130132 p31779 p130115 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130137 :=
@BSN.sin_arg_round false (nat_lit 800166) (nat_lit 1048576) (nat_lit 131182686233243150188544)
  (nat_lit 151115727451828646838272) (nat_lit 1864218095) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130135 (p130136 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130138 :=
p130130 (nat_lit 800166) (nat_lit 1048576) (nat_lit 24) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130113 BSN.pi_near_15 p130137 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130139 :=
@p130129 (nat_lit 1) (nat_lit 4096) true (nat_lit 800166) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130109 (nat_lit 250000000000000000) (nat_lit 162325997) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130111 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 162325997) (nat_lit 1048576))
  (p130138 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130140 :=
p130126
  (@p130127 (nat_lit 3189) (nat_lit 12800000)
    (@p130128 (nat_lit 204096) (nat_lit 819200000) (nat_lit 400083) (nat_lit 524288) (nat_lit 3189)
      (nat_lit 12800000) (p130139 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130141 :=
@p130105 (nat_lit 145048879325) (nat_lit 1099511627776) (nat_lit 35371313147)
  (nat_lit 687194767360000) false (nat_lit 85633365237) (nat_lit 549755813888) (nat_lit 17723935011)
  (nat_lit 343597383680000) (p130124 (Eq.refl true)) p130140

noncomputable def p130142 :=
@p129782 false (nat_lit 699151170333048832000) (nat_lit 20347977125) (nat_lit 549755813888)
  (nat_lit 128436149751) (nat_lit 68719476736000)
  (@p129783 (nat_lit 1251737944363) (nat_lit 687194767360000) true (nat_lit 4080336757)
    (nat_lit 34359738368) (nat_lit 39028550859) (nat_lit 21474836480000)
    (p129097 (nat_lit 23) (nat_lit 24) (Eq.refl true) (Eq.refl true))
    p130101)
  (p130104 p130141)

noncomputable def p130143 :=
p130142 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130144 :=
p130143 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d1198 : p129778 (nat_lit 68719476736000) :=
@p129779 (nat_lit 128710925751) (nat_lit 68719476736000) false (nat_lit 20347977125)
  (nat_lit 549755813888) (nat_lit 128436149751) (nat_lit 68719476736000)
  (p129097 (nat_lit 24) (nat_lit 25) (Eq.refl true) (Eq.refl true))
  p130144

end RHHeight1000.EMHead24At48711

theorem localSolutionEmHead24 : let z : ℂ := ∑ n ∈ Finset.Ico (1 : ℕ) 25,
      (n : ℂ) ^ (-((1 : ℂ) / 2 + Complex.I * (((48711 : ℝ) / 1000 : ℝ) : ℂ)))
  |z.re - (39429631493 : ℝ) / 68719476736| ≤ (128710925751 : ℝ) / 68719476736000 ∧
  |z.im - (20347977125 : ℝ) / 549755813888| ≤ (128436149751 : ℝ) / 68719476736000 := by
  simpa [BSN.headSumC, Enclosure.Complex.IsNear, Enclosure.Real.IsNear, Enclosure.sfrac] using (show Enclosure.Complex.IsNear
  (BSN.headSumC
    (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
      (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex
        (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
        (@OfNat.ofNat.{0} Complex (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
        ↑(Enclosure.sfrac Bool.false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))))
    (nat_lit 25))
  Bool.false (nat_lit 39429631493) (nat_lit 68719476736) (nat_lit 128710925751) (nat_lit 68719476736000) Bool.false
  (nat_lit 20347977125) (nat_lit 549755813888) (nat_lit 128436149751) (nat_lit 68719476736000) from RHHeight1000.EMHead24At48711.d1198)

theorem RHHeight1000.em_t48711_head24_enclosure : let z : ℂ := ∑ n ∈ Finset.Ico (1 : ℕ) 25,
      (n : ℂ) ^ (-((1 : ℂ) / 2 + Complex.I * (((48711 : ℝ) / 1000 : ℝ) : ℂ)))
  |z.re - (39429631493 : ℝ) / 68719476736| ≤ (128710925751 : ℝ) / 68719476736000 ∧
  |z.im - (20347977125 : ℝ) / 549755813888| ≤ (128436149751 : ℝ) / 68719476736000 := localSolutionEmHead24
#print axioms RHHeight1000.em_t48711_head24_enclosure

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false
set_option linter.auxLemma false
open scoped BigOperators

namespace RHHeight1000.EMHead40At48711
noncomputable def p30091 :=
@BSN.binarySplit_of_base5 (BSN.artanhP (nat_lit 13)) (BSN.artanhQ (nat_lit 45)) (nat_lit 0) (nat_lit 5)
  (nat_lit 10371179520995104305) (nat_lit 353956287581982421875) (nat_lit 130276274797305) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p31525 :=
nat_lit 2552117751907038475975309555738261585920

noncomputable def p31526 :=
nat_lit 17864824263349269331827166890167831101440

noncomputable def p31541 :=
nat_lit 510423550381407695195061911147652317184

noncomputable def p31542 :=
nat_lit 7656353255721115427925928667214784757760

noncomputable def p31681 :=
nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def p31684 :=
nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def p31776 :=
nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def p31779 :=
nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def p32549 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25)))) false
  (nat_lit 209715) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32550 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25))) (nat_lit 5242881)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 104857) (nat_lit 104858)

noncomputable def p32551 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5242881) (nat_lit 1048576)

noncomputable def p32552 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5242881) (nat_lit 1048576)

noncomputable def p32553 :=
@p32552 (nat_lit 1) (nat_lit 1048576) (nat_lit 5242881) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 25) (nat_lit 1) (nat_lit 2621440) (nat_lit 2621441) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32554 :=
@p32550 (nat_lit 524288)
  (@p32551 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 25))
    (p32553 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32559 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 60802810194841294602240) (nat_lit 18889465931478580854784)

noncomputable def p32560 :=
BSN.log_rat_reduce_isNear (nat_lit 25) (nat_lit 1) (nat_lit 4) (nat_lit 50) (nat_lit 32) (nat_lit 233982)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32561 :=
BSN.log_dyadic_bound (nat_lit 9) (nat_lit 41) (nat_lit 5) (nat_lit 4) (nat_lit 7545754341519345) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 124828057765224) (nat_lit 4519905705) (nat_lit 233982) (nat_lit 50)

noncomputable def p32562 :=
p32561 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32563 :=
@BSN.binarySplit_of_base4 (BSN.artanhP (nat_lit 9)) (BSN.artanhQ (nat_lit 41)) (nat_lit 0) (nat_lit 4)
  (nat_lit 124828057765224) (nat_lit 7545754341519345) (nat_lit 4519905705) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32564 :=
p32560 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32562 (p32563 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32598 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26)))) false
  (nat_lit 205643) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32599 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26))) (nat_lit 5346709)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 102821) (nat_lit 102822)

noncomputable def p32600 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5346709) (nat_lit 1048576)

noncomputable def p32601 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5346709) (nat_lit 1048576)

noncomputable def p32602 :=
@p32601 (nat_lit 1) (nat_lit 1048576) (nat_lit 5346709) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 26) (nat_lit 1) (nat_lit 2673354) (nat_lit 2673355) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32603 :=
@p32599 (nat_lit 524288)
  (@p32600 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 26))
    (p32602 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32608 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 61543670347942250676224) (nat_lit 18889465931478580854784)

noncomputable def p32609 :=
BSN.log_rat_reduce_isNear (nat_lit 26) (nat_lit 1) (nat_lit 4) (nat_lit 52) (nat_lit 32) (nat_lit 254545)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32610 :=
BSN.log_dyadic_bound (nat_lit 10) (nat_lit 42) (nat_lit 5) (nat_lit 4) (nat_lit 9150106136613120) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 179034245376000) (nat_lit 10500000000) (nat_lit 254545) (nat_lit 52)

noncomputable def p32611 :=
p32610 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32612 :=
@BSN.binarySplit_of_base4 (BSN.artanhP (nat_lit 10)) (BSN.artanhQ (nat_lit 42)) (nat_lit 0) (nat_lit 4)
  (nat_lit 179034245376000) (nat_lit 9150106136613120) (nat_lit 10500000000) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32613 :=
p32609 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32611 (p32612 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32648 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27)))) false
  (nat_lit 201799) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32649 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27))) (nat_lit 5448561)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 100899) (nat_lit 100900)

noncomputable def p32650 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5448561) (nat_lit 1048576)

noncomputable def p32651 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5448561) (nat_lit 1048576)

noncomputable def p32652 :=
@p32651 (nat_lit 1) (nat_lit 1048576) (nat_lit 5448561) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 27) (nat_lit 1) (nat_lit 2724280) (nat_lit 2724281) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32653 :=
@p32649 (nat_lit 524288)
  (@p32650 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 27))
    (p32652 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32658 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 62256572154556490711040) (nat_lit 18889465931478580854784)

noncomputable def p32659 :=
BSN.log_rat_reduce_isNear (nat_lit 27) (nat_lit 1) (nat_lit 4) (nat_lit 54) (nat_lit 32) (nat_lit 274332)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32660 :=
BSN.log_dyadic_bound (nat_lit 11) (nat_lit 43) (nat_lit 5) (nat_lit 4) (nat_lit 11045349262332945) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 250863800262504) (nat_lit 22507682505) (nat_lit 274332) (nat_lit 54)

noncomputable def p32661 :=
p32660 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32662 :=
@BSN.binarySplit_of_base4 (BSN.artanhP (nat_lit 11)) (BSN.artanhQ (nat_lit 43)) (nat_lit 0) (nat_lit 4)
  (nat_lit 250863800262504) (nat_lit 11045349262332945) (nat_lit 22507682505) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32663 :=
p32659 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32661 (p32662 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32699 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28)))) false
  (nat_lit 198163) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32700 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28))) (nat_lit 5548543)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 99081) (nat_lit 99082)

noncomputable def p32701 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5548543) (nat_lit 1048576)

noncomputable def p32702 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5548543) (nat_lit 1048576)

noncomputable def p32703 :=
@p32702 (nat_lit 1) (nat_lit 1048576) (nat_lit 5548543) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 28) (nat_lit 1) (nat_lit 2774271) (nat_lit 2774272) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32704 :=
@p32700 (nat_lit 524288)
  (@p32701 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 28))
    (p32703 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32709 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 62943533227317076688896) (nat_lit 18889465931478580854784)

noncomputable def p32710 :=
BSN.log_rat_reduce_isNear (nat_lit 28) (nat_lit 1) (nat_lit 4) (nat_lit 56) (nat_lit 32) (nat_lit 293399)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32711 :=
BSN.log_dyadic_bound (nat_lit 12) (nat_lit 44) (nat_lit 5) (nat_lit 4) (nat_lit 13275571325829120) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 344661139390464) (nat_lit 45148078080) (nat_lit 293399) (nat_lit 56)

noncomputable def p32712 :=
p32711 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32713 :=
@BSN.binarySplit_of_base4 (BSN.artanhP (nat_lit 12)) (BSN.artanhQ (nat_lit 44)) (nat_lit 0) (nat_lit 4)
  (nat_lit 344661139390464) (nat_lit 13275571325829120) (nat_lit 45148078080) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32714 :=
p32710 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32712 (p32713 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32750 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29)))) false
  (nat_lit 194715) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32751 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29))) (nat_lit 5646755)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 97357) (nat_lit 97358)

noncomputable def p32752 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5646755) (nat_lit 1048576)

noncomputable def p32753 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5646755) (nat_lit 1048576)

noncomputable def p32754 :=
@p32753 (nat_lit 1) (nat_lit 1048576) (nat_lit 5646755) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 29) (nat_lit 1) (nat_lit 2823377) (nat_lit 2823378) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32755 :=
@p32751 (nat_lit 524288)
  (@p32752 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 29))
    (p32754 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32760 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 63606391034871975772160) (nat_lit 18889465931478580854784)

noncomputable def p32761 :=
BSN.log_rat_reduce_isNear (nat_lit 29) (nat_lit 1) (nat_lit 4) (nat_lit 58) (nat_lit 32) (nat_lit 311797)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32762 :=
BSN.log_dyadic_bound (nat_lit 13) (nat_lit 45) (nat_lit 6) (nat_lit 5) (nat_lit 353956287581982421875) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 10371179520995104305) (nat_lit 130276274797305) (nat_lit 311797) (nat_lit 58)

noncomputable def p32763 :=
p32762 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32764 :=
p32761 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32763 (p30091 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32800 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30)))) false
  (nat_lit 191443) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32801 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30))) (nat_lit 5743287)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 95721) (nat_lit 95722)

noncomputable def p32802 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5743287) (nat_lit 1048576)

noncomputable def p32803 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5743287) (nat_lit 1048576)

noncomputable def p32804 :=
@p32803 (nat_lit 1) (nat_lit 1048576) (nat_lit 5743287) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 30) (nat_lit 1) (nat_lit 2871643) (nat_lit 2871644) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32805 :=
@p32801 (nat_lit 524288)
  (@p32802 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 30))
    (p32804 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32810 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 64246766873087041339392) (nat_lit 18889465931478580854784)

noncomputable def p32811 :=
BSN.log_rat_reduce_isNear (nat_lit 30) (nat_lit 1) (nat_lit 4) (nat_lit 60) (nat_lit 32) (nat_lit 329571)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32812 :=
BSN.log_dyadic_bound (nat_lit 14) (nat_lit 46) (nat_lit 6) (nat_lit 5) (nat_lit 440963670083462507520) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 14425761949190022144) (nat_lit 273345648952320) (nat_lit 329571) (nat_lit 60)

noncomputable def p32813 :=
p32812 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32814 :=
@BSN.binarySplit_of_base5 (BSN.artanhP (nat_lit 14)) (BSN.artanhQ (nat_lit 46)) (nat_lit 0) (nat_lit 5)
  (nat_lit 14425761949190022144) (nat_lit 440963670083462507520) (nat_lit 273345648952320) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32815 :=
p32811 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32813 (p32814 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32851 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31)))) false
  (nat_lit 188329) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32852 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31))) (nat_lit 5838225)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 94164) (nat_lit 94165)

noncomputable def p32853 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5838225) (nat_lit 1048576)

noncomputable def p32854 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5838225) (nat_lit 1048576)

noncomputable def p32855 :=
@p32854 (nat_lit 1) (nat_lit 1048576) (nat_lit 5838225) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 31) (nat_lit 1) (nat_lit 2919112) (nat_lit 2919113) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32856 :=
@p32852 (nat_lit 524288)
  (@p32853 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 31))
    (p32855 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32861 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 64866173951437069877248) (nat_lit 18889465931478580854784)

noncomputable def p32862 :=
BSN.log_rat_reduce_isNear (nat_lit 31) (nat_lit 1) (nat_lit 4) (nat_lit 62) (nat_lit 32) (nat_lit 346763)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32863 :=
BSN.log_dyadic_bound (nat_lit 15) (nat_lit 47) (nat_lit 6) (nat_lit 5) (nat_lit 546767979591453359355) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 19788004106328479625) (nat_lit 544934619140625) (nat_lit 346763) (nat_lit 62)

noncomputable def p32864 :=
p32863 (nat_lit 32) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32865 :=
@BSN.binarySplit_of_base5 (BSN.artanhP (nat_lit 15)) (BSN.artanhQ (nat_lit 47)) (nat_lit 0) (nat_lit 5)
  (nat_lit 19788004106328479625) (nat_lit 546767979591453359355) (nat_lit 544934619140625) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32866 :=
p32862 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p32864 (p32865 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p32902 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32)))) false
  (nat_lit 185363) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p32903 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32))) (nat_lit 5931641)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 92681) (nat_lit 92682)

noncomputable def p32904 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5931641) (nat_lit 1048576)

noncomputable def p32905 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 5931641) (nat_lit 1048576)

noncomputable def p32906 :=
@p32905 (nat_lit 1) (nat_lit 1048576) (nat_lit 5931641) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 32) (nat_lit 1) (nat_lit 2965820) (nat_lit 2965821) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p32907 :=
@p32903 (nat_lit 524288)
  (@p32904 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 32))
    (p32906 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p32912 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 65465900263437584302080) (nat_lit 18889465931478580854784)

noncomputable def p32913 :=
BSN.log_rat_reduce_isNear (nat_lit 32) (nat_lit 1) (nat_lit 5) (nat_lit 64) (nat_lit 64) (nat_lit 0) (nat_lit 524288)
  (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p32914 :=
BSN.log_dyadic_bound (nat_lit 0) (nat_lit 64) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 524288) (nat_lit 200000)
  (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 64)

noncomputable def p32915 :=
p32914 (nat_lit 64) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32916 :=
p32915
  (@BSN.binarySplit_of_le (BSN.artanhP (nat_lit 0)) (BSN.artanhQ (nat_lit 64)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p32917 :=
p32913 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) p32916 BSN.log2_near_15 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p32999 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33)))) false
  (nat_lit 182533) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p33000 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33))) (nat_lit 6023611)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 91266) (nat_lit 91267)

noncomputable def p33001 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6023611) (nat_lit 1048576)

noncomputable def p33002 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6023611) (nat_lit 1048576)

noncomputable def p33003 :=
@p33002 (nat_lit 1) (nat_lit 1048576) (nat_lit 6023611) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 33) (nat_lit 1) (nat_lit 3011805) (nat_lit 3011806) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p33004 :=
@p33000 (nat_lit 524288)
  (@p33001 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 33))
    (p33003 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33009 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 66047152845744529997824) (nat_lit 18889465931478580854784)

noncomputable def p33010 :=
BSN.log_rat_reduce_isNear (nat_lit 33) (nat_lit 1) (nat_lit 5) (nat_lit 66) (nat_lit 64) (nat_lit 16133)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p33011 :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 65) (nat_lit 2) (nat_lit 1) (nat_lit 12675) (nat_lit 524288) (nat_lit 200000)
  (nat_lit 1) (nat_lit 1) (nat_lit 16133) (nat_lit 66)

noncomputable def p33012 :=
p33011 (nat_lit 64) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33013 :=
@BSN.binarySplit_of_base (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 65)) (nat_lit 0) (nat_lit 1) (nat_lit 1)
  (nat_lit 12675) (nat_lit 1) (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33014 :=
p33010 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p33012 (p33013 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p33049 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34)))) false
  (nat_lit 179829) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p33050 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34))) (nat_lit 6114197)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 89914) (nat_lit 89915)

noncomputable def p33051 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6114197) (nat_lit 1048576)

noncomputable def p33052 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6114197) (nat_lit 1048576)

noncomputable def p33053 :=
@p33052 (nat_lit 1) (nat_lit 1048576) (nat_lit 6114197) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 34) (nat_lit 1) (nat_lit 3057098) (nat_lit 3057099) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p33054 :=
@p33050 (nat_lit 524288)
  (@p33051 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 34))
    (p33053 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33059 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 66611039547888335060992) (nat_lit 18889465931478580854784)

noncomputable def p33060 :=
BSN.log_rat_reduce_isNear (nat_lit 34) (nat_lit 1) (nat_lit 5) (nat_lit 68) (nat_lit 64) (nat_lit 31784)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p33061 :=
BSN.log_dyadic_bound (nat_lit 2) (nat_lit 66) (nat_lit 2) (nat_lit 1) (nat_lit 13068) (nat_lit 524288) (nat_lit 200000)
  (nat_lit 4) (nat_lit 4) (nat_lit 31784) (nat_lit 68)

noncomputable def p33062 :=
p33061 (nat_lit 64) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33063 :=
@BSN.binarySplit_of_base (BSN.artanhP (nat_lit 2)) (BSN.artanhQ (nat_lit 66)) (nat_lit 0) (nat_lit 1) (nat_lit 4)
  (nat_lit 13068) (nat_lit 4) (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33064 :=
p33060 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p33062 (p33063 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p33100 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35)))) false
  (nat_lit 177241) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p33101 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35))) (nat_lit 6203459)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 88620) (nat_lit 88621)

noncomputable def p33102 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6203459) (nat_lit 1048576)

noncomputable def p33103 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6203459) (nat_lit 1048576)

noncomputable def p33104 :=
@p33103 (nat_lit 1) (nat_lit 1048576) (nat_lit 6203459) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 35) (nat_lit 1) (nat_lit 3101729) (nat_lit 3101730) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p33105 :=
@p33101 (nat_lit 524288)
  (@p33102 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 35))
    (p33104 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33110 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 67158605204982549446656) (nat_lit 18889465931478580854784)

noncomputable def p33111 :=
BSN.log_rat_reduce_isNear (nat_lit 35) (nat_lit 1) (nat_lit 5) (nat_lit 70) (nat_lit 64) (nat_lit 46982)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p33112 :=
BSN.log_dyadic_bound (nat_lit 3) (nat_lit 67) (nat_lit 2) (nat_lit 1) (nat_lit 13467) (nat_lit 524288) (nat_lit 200000)
  (nat_lit 9) (nat_lit 9) (nat_lit 46982) (nat_lit 70)

noncomputable def p33113 :=
p33112 (nat_lit 64) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33114 :=
@BSN.binarySplit_of_base (BSN.artanhP (nat_lit 3)) (BSN.artanhQ (nat_lit 67)) (nat_lit 0) (nat_lit 1) (nat_lit 9)
  (nat_lit 13467) (nat_lit 9) (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33115 :=
p33111 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p33113 (p33114 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p33151 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36)))) false
  (nat_lit 174763) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p33152 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36))) (nat_lit 6291457)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 87381) (nat_lit 87382)

noncomputable def p33153 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6291457) (nat_lit 1048576)

noncomputable def p33154 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6291457) (nat_lit 1048576)

noncomputable def p33155 :=
@p33154 (nat_lit 1) (nat_lit 1048576) (nat_lit 6291457) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 36) (nat_lit 1) (nat_lit 3145728) (nat_lit 3145729) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p33156 :=
@p33152 (nat_lit 524288)
  (@p33153 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 36))
    (p33155 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33161 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 67690750536952647254016) (nat_lit 18889465931478580854784)

noncomputable def p33162 :=
BSN.log_rat_reduce_isNear (nat_lit 36) (nat_lit 1) (nat_lit 5) (nat_lit 72) (nat_lit 64) (nat_lit 61752)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p33163 :=
BSN.log_dyadic_bound (nat_lit 4) (nat_lit 68) (nat_lit 3) (nat_lit 2) (nat_lit 320720640) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 370688) (nat_lit 768) (nat_lit 61752) (nat_lit 72)

noncomputable def p33164 :=
p33163 (nat_lit 64) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33165 :=
@BSN.binarySplit_of_base2 (BSN.artanhP (nat_lit 4)) (BSN.artanhQ (nat_lit 68)) (nat_lit 0) (nat_lit 2) (nat_lit 370688)
  (nat_lit 320720640) (nat_lit 768) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33166 :=
p33162 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p33164 (p33165 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p33202 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37)))) false
  (nat_lit 172385) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p33203 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37))) (nat_lit 6378239)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 86192) (nat_lit 86193)

noncomputable def p33204 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6378239) (nat_lit 1048576)

noncomputable def p33205 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6378239) (nat_lit 1048576)

noncomputable def p33206 :=
@p33205 (nat_lit 1) (nat_lit 1048576) (nat_lit 6378239) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 37) (nat_lit 1) (nat_lit 3189119) (nat_lit 3189120) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p33207 :=
@p33203 (nat_lit 524288)
  (@p33204 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 37))
    (p33206 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33212 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 68208304206130064654336) (nat_lit 18889465931478580854784)

noncomputable def p33213 :=
BSN.log_rat_reduce_isNear (nat_lit 37) (nat_lit 1) (nat_lit 5) (nat_lit 74) (nat_lit 64) (nat_lit 76117)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p33214 :=
BSN.log_dyadic_bound (nat_lit 5) (nat_lit 69) (nat_lit 3) (nat_lit 2) (nat_lit 340006815) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 597000) (nat_lit 1875) (nat_lit 76117) (nat_lit 74)

noncomputable def p33215 :=
p33214 (nat_lit 64) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33216 :=
@BSN.binarySplit_of_base2 (BSN.artanhP (nat_lit 5)) (BSN.artanhQ (nat_lit 69)) (nat_lit 0) (nat_lit 2) (nat_lit 597000)
  (nat_lit 340006815) (nat_lit 1875) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33217 :=
p33213 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p33215 (p33216 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p33253 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38)))) false
  (nat_lit 170101) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p33254 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38))) (nat_lit 6463857)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 85050) (nat_lit 85051)

noncomputable def p33255 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6463857) (nat_lit 1048576)

noncomputable def p33256 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6463857) (nat_lit 1048576)

noncomputable def p33257 :=
@p33256 (nat_lit 1) (nat_lit 1048576) (nat_lit 6463857) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 38) (nat_lit 1) (nat_lit 3231928) (nat_lit 3231929) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p33258 :=
@p33254 (nat_lit 524288)
  (@p33255 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 38))
    (p33257 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33263 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 68712058846049218854912) (nat_lit 18889465931478580854784)

noncomputable def p33264 :=
BSN.log_rat_reduce_isNear (nat_lit 38) (nat_lit 1) (nat_lit 5) (nat_lit 76) (nat_lit 64) (nat_lit 90099)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p33265 :=
BSN.log_dyadic_bound (nat_lit 6) (nat_lit 70) (nat_lit 3) (nat_lit 2) (nat_lit 360150000) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 885888) (nat_lit 3888) (nat_lit 90099) (nat_lit 76)

noncomputable def p33266 :=
p33265 (nat_lit 64) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33267 :=
@BSN.binarySplit_of_base2 (BSN.artanhP (nat_lit 6)) (BSN.artanhQ (nat_lit 70)) (nat_lit 0) (nat_lit 2) (nat_lit 885888)
  (nat_lit 360150000) (nat_lit 3888) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33268 :=
p33264 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p33266 (p33267 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p33304 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39)))) false
  (nat_lit 167907) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p33305 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39))) (nat_lit 6548355)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 83953) (nat_lit 83954)

noncomputable def p33306 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6548355) (nat_lit 1048576)

noncomputable def p33307 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6548355) (nat_lit 1048576)

noncomputable def p33308 :=
@p33307 (nat_lit 1) (nat_lit 1048576) (nat_lit 6548355) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 39) (nat_lit 1) (nat_lit 3274177) (nat_lit 3274178) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p33309 :=
@p33305 (nat_lit 524288)
  (@p33306 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 39))
    (p33308 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33314 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 69202699003853470171136) (nat_lit 18889465931478580854784)

noncomputable def p33315 :=
BSN.log_rat_reduce_isNear (nat_lit 39) (nat_lit 1) (nat_lit 5) (nat_lit 78) (nat_lit 64) (nat_lit 103717)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p33316 :=
BSN.log_dyadic_bound (nat_lit 7) (nat_lit 71) (nat_lit 3) (nat_lit 2) (nat_lit 381175215) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 1242248) (nat_lit 7203) (nat_lit 103717) (nat_lit 78)

noncomputable def p33317 :=
p33316 (nat_lit 64) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33318 :=
@BSN.binarySplit_of_base2 (BSN.artanhP (nat_lit 7)) (BSN.artanhQ (nat_lit 71)) (nat_lit 0) (nat_lit 2) (nat_lit 1242248)
  (nat_lit 381175215) (nat_lit 7203) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33319 :=
p33315 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p33317 (p33318 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p33355 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40)))) false
  (nat_lit 165795) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576)

noncomputable def p33356 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40))) (nat_lit 6631777)
  (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) (nat_lit 82897) (nat_lit 82898)

noncomputable def p33357 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40)))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6631777) (nat_lit 1048576)

noncomputable def p33358 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 6631777) (nat_lit 1048576)

noncomputable def p33359 :=
@p33358 (nat_lit 1) (nat_lit 1048576) (nat_lit 6631777) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 1048576)
  (BSN.sqrt_enclosure (nat_lit 40) (nat_lit 1) (nat_lit 3315888) (nat_lit 3315889) (nat_lit 524288)
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p33360 :=
@p33356 (nat_lit 524288)
  (@p33357 (nat_lit 1) (nat_lit 1048576) (BSN.sqrt_natCast_div_one (nat_lit 40))
    (p33359 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p33365 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1))))
  false (nat_lit 69680945255483197882368) (nat_lit 18889465931478580854784)

noncomputable def p33366 :=
BSN.log_rat_reduce_isNear (nat_lit 40) (nat_lit 1) (nat_lit 5) (nat_lit 80) (nat_lit 64) (nat_lit 116991)
  (nat_lit 524288) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 200000) (nat_lit 1000000000000000)

noncomputable def p33367 :=
BSN.log_dyadic_bound (nat_lit 8) (nat_lit 72) (nat_lit 3) (nat_lit 2) (nat_lit 403107840) (nat_lit 524288)
  (nat_lit 200000) (nat_lit 1671168) (nat_lit 12288) (nat_lit 116991) (nat_lit 80)

noncomputable def p33368 :=
p33367 (nat_lit 64) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33369 :=
@BSN.binarySplit_of_base2 (BSN.artanhP (nat_lit 8)) (BSN.artanhQ (nat_lit 72)) (nat_lit 0) (nat_lit 2) (nat_lit 1671168)
  (nat_lit 403107840) (nat_lit 12288) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p33370 :=
p33366 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p33368 (p33369 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p129093 :=
BSN.headSumC
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex
      (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
      (@OfNat.ofNat.{0} Complex (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
    (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
      ↑(Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))))

noncomputable def p129095 :=
@Neg.neg.{0} Complex Complex.instNeg
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex
      (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
      (@OfNat.ofNat.{0} Complex (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
    (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
      ↑(Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))))

noncomputable def p129097 :=
BSN.head_sum_c_succ
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex
      (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
      (@OfNat.ofNat.{0} Complex (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
    (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
      ↑(Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))))

theorem d1198 : Enclosure.Complex.IsNear
  (BSN.headSumC
    (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
      (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex
        (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
        (@OfNat.ofNat.{0} Complex (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
        ↑(Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))))
    (nat_lit 25))
  false (nat_lit 39429631493) (nat_lit 68719476736) (nat_lit 128710925751) (nat_lit 68719476736000) false
  (nat_lit 20347977125) (nat_lit 549755813888) (nat_lit 128436149751) (nat_lit 68719476736000) := by
  simpa [BSN.headSumC, Enclosure.Complex.IsNear, Enclosure.Real.IsNear, Enclosure.sfrac] using RHHeight1000.em_t48711_head24_enclosure

noncomputable def p130145 :=
Enclosure.Complex.IsNear (p129093 (nat_lit 33)) false (nat_lit 748337629977)
  (nat_lit 1099511627776) (nat_lit 7742033207027) (nat_lit 3435973836800000) false (nat_lit 141105362441)
  (nat_lit 1099511627776) (nat_lit 7728036732027)

noncomputable def p130146 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 33))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 32))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 32)) p129095))
  false (nat_lit 748337629977) (nat_lit 1099511627776)

noncomputable def p130147 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 32))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 32)) p129095)
  false (nat_lit 308334457775) (nat_lit 549755813888) (nat_lit 3793952981313)

noncomputable def p130148 :=
@p130147 (nat_lit 1717986918400000) true (nat_lit 934876767) (nat_lit 549755813888)
  (nat_lit 3786859437563) (nat_lit 1717986918400000) false (nat_lit 131668714427) (nat_lit 1099511627776)
  (nat_lit 154127244401) (nat_lit 3435973836800000)

noncomputable def p130149 :=
@p130148 false (nat_lit 142975115975) (nat_lit 1099511627776) (nat_lit 154317856901)
  (nat_lit 3435973836800000) false (nat_lit 411402962831022621720576) (nat_lit 748337629977)
  (nat_lit 1099511627776) (nat_lit 7742033207027) (nat_lit 3435973836800000)

noncomputable def p130150 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 32))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 31))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 31)) p129095))
  false (nat_lit 308334457775) (nat_lit 549755813888)

noncomputable def p130151 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 31))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 31)) p129095)
  false (nat_lit 379322061061) (nat_lit 549755813888) (nat_lit 3715900263203)

noncomputable def p130152 :=
@p130151 (nat_lit 1717986918400000) true (nat_lit 34782394651) (nat_lit 274877906944)
  (nat_lit 231802865083) (nat_lit 107374182400000) true (nat_lit 35493801643) (nat_lit 274877906944)
  (nat_lit 7805271811) (nat_lit 171798691840000)

noncomputable def p130153 :=
@p130152 false (nat_lit 68629912535) (nat_lit 549755813888) (nat_lit 15602719247)
  (nat_lit 343597383680000) false (nat_lit 84754330391905147289600) (nat_lit 308334457775) (nat_lit 549755813888)
  (nat_lit 3793952981313) (nat_lit 1717986918400000)

noncomputable def p130154 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 31))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 30))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 30)) p129095))
  false (nat_lit 379322061061) (nat_lit 549755813888)

noncomputable def p130155 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 30))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 30)) p129095)
  false (nat_lit 447150698847) (nat_lit 549755813888) (nat_lit 727329432041)

noncomputable def p130156 :=
@p130155 (nat_lit 343597383680000) false (nat_lit 4419315263) (nat_lit 549755813888)
  (nat_lit 725898452041) (nat_lit 343597383680000) true (nat_lit 33914318893) (nat_lit 274877906944)
  (nat_lit 39626551499) (nat_lit 858993459200000)

noncomputable def p130157 :=
@p130156 true (nat_lit 73984104565) (nat_lit 549755813888) (nat_lit 79353581123)
  (nat_lit 1717986918400000) false (nat_lit 104267254202131843907584) (nat_lit 379322061061) (nat_lit 549755813888)
  (nat_lit 3715900263203) (nat_lit 1717986918400000)

noncomputable def p130158 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 30))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 29))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 29)) p129095))
  false (nat_lit 447150698847) (nat_lit 549755813888)

noncomputable def p130159 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 29))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 29)) p129095)
  false (nat_lit 733188170529) (nat_lit 1099511627776) (nat_lit 7111137084091)

noncomputable def p130160 :=
@p130159 (nat_lit 3435973836800000) false (nat_lit 134255146171) (nat_lit 1099511627776)
  (nat_lit 7097400184091) (nat_lit 3435973836800000) false (nat_lit 161113227165) (nat_lit 1099511627776)
  (nat_lit 162157236319) (nat_lit 3435973836800000)

noncomputable def p130161 :=
@p130160 true (nat_lit 125416515645) (nat_lit 1099511627776) (nat_lit 161584336319)
  (nat_lit 3435973836800000) false (nat_lit 983294785500881872748544) (nat_lit 447150698847) (nat_lit 549755813888)
  (nat_lit 727329432041) (nat_lit 343597383680000)

noncomputable def p130162 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 29))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 28))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 28)) p129095))
  false (nat_lit 733188170529) (nat_lit 1099511627776)

noncomputable def p130163 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 28))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 28)) p129095)
  false (nat_lit 314708571567) (nat_lit 549755813888) (nat_lit 694710344949)

noncomputable def p130164 :=
@p130163 (nat_lit 343597383680000) true (nat_lit 45766427505) (nat_lit 1099511627776)
  (nat_lit 1386432818023) (nat_lit 687194767360000) false (nat_lit 103771027395) (nat_lit 1099511627776)
  (nat_lit 164033634601) (nat_lit 3435973836800000)

noncomputable def p130165 :=
@p130164 false (nat_lit 45005393419) (nat_lit 274877906944) (nat_lit 20654511747)
  (nat_lit 429496729600000) false (nat_lit 403074459422224130506752) (nat_lit 733188170529) (nat_lit 1099511627776)
  (nat_lit 7111137084091) (nat_lit 3435973836800000)

noncomputable def p130166 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 28))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 27))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 27)) p129095))
  false (nat_lit 314708571567) (nat_lit 549755813888)

noncomputable def p130167 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 27))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 27)) p129095)
  false (nat_lit 830128648323) (nat_lit 1099511627776) (nat_lit 1355723674783)

noncomputable def p130168 :=
@p130167 (nat_lit 687194767360000) true (nat_lit 112774189053) (nat_lit 1099511627776)
  (nat_lit 1353149902283) (nat_lit 687194767360000) true (nat_lit 200711505189) (nat_lit 1099511627776)
  (nat_lit 6739403023) (nat_lit 137438953472000)

noncomputable def p130169 :=
@p130168 false (nat_lit 16751940387) (nat_lit 274877906944) (nat_lit 1664145787)
  (nat_lit 34359738368000) false (nat_lit 692051467597383922089984) (nat_lit 314708571567) (nat_lit 549755813888)
  (nat_lit 694710344949) (nat_lit 343597383680000)

noncomputable def p130170 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 27))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 26))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 26)) p129095))
  false (nat_lit 830128648323) (nat_lit 1099511627776)

noncomputable def p130171 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 26))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 26)) p129095)
  false (nat_lit 841901710073) (nat_lit 1099511627776) (nat_lit 6610554996369)

noncomputable def p130172 :=
@p130171 (nat_lit 3435973836800000) false (nat_lit 25634073505) (nat_lit 274877906944)
  (nat_lit 824324141343) (nat_lit 429496729600000) true (nat_lit 5886530875) (nat_lit 549755813888)
  (nat_lit 84031688773) (nat_lit 1717986918400000)

noncomputable def p130173 :=
@p130172 true (nat_lit 215310483073) (nat_lit 1099511627776) (nat_lit 171156380671)
  (nat_lit 3435973836800000) false (nat_lit 456368050690556191309824) (nat_lit 830128648323)
  (nat_lit 1099511627776) (nat_lit 1355723674783) (nat_lit 687194767360000)

noncomputable def p130174 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 26))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 25))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 25)) p129095))
  false (nat_lit 841901710073) (nat_lit 1099511627776)

noncomputable def p130175 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 25))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 25)) p129095)
  false (nat_lit 39429631493) (nat_lit 68719476736) (nat_lit 128710925751)

noncomputable def p130176 :=
@p130175 (nat_lit 68719476736000) false (nat_lit 20347977125) (nat_lit 549755813888)
  (nat_lit 128436149751) (nat_lit 68719476736000) false (nat_lit 211027606185) (nat_lit 1099511627776)
  (nat_lit 175008708819) (nat_lit 3435973836800000)

noncomputable def p130177 :=
@p130176 false (nat_lit 30920169885) (nat_lit 549755813888) (nat_lit 86392821597)
  (nat_lit 1717986918400000) false (nat_lit 57855044979360140361728) (nat_lit 841901710073) (nat_lit 1099511627776)
  (nat_lit 6610554996369) (nat_lit 3435973836800000)

noncomputable def p130178 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 25)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1)))))) }

noncomputable def p130179 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 25)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130180 :=
@p130178 false (nat_lit 211027606185) (nat_lit 1099511627776) (nat_lit 175008708819)
  (nat_lit 3435973836800000) false (nat_lit 30920169885) (nat_lit 549755813888) (nat_lit 86392821597)
  (nat_lit 1717986918400000) p130179

noncomputable def p130181 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1)))))))
  false

noncomputable def p130182 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1)))))
  (nat_lit 209715) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130183 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1)))))
  false (nat_lit 1006259) (nat_lit 1048576)

noncomputable def p130184 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 82205511)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 82205511) (nat_lit 524288)

noncomputable def p130185 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1))))
  false (nat_lit 35306998341094425933) (nat_lit 225179981368524800) (nat_lit 60888750048711)

noncomputable def p130186 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3624129903009015) (nat_lit 1125899906842624)

noncomputable def p130187 :=
@p130186 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 35306998341094425933)
  (nat_lit 225179981368524800) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 25) (nat_lit 1) (nat_lit 3624129903009015) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32559 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3624129903009015)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32564 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130188 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 82205511)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 97147213324416693829632))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130189 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 82205511) (nat_lit 524288) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 24) (nat_lit 97147213324416693829632) (nat_lit 75557863725914323419136)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130190 :=
nat_lit 3741241219842236806595619353809078918262090297697223701525737263483078555996705

noncomputable def p130191 :=
nat_lit 3377880952890531344969696395380653461991796531489466436640330622892317086241

noncomputable def p130192 :=
nat_lit 9793019958996416490334766418193161823176535490060793415479513250018618180899361

noncomputable def p130193 :=
BSN.sin_dyadic_bound_f (nat_lit 2761089869) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130190 p31776 p130191
  p130192 p31779

noncomputable def p130194 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 2761089869)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130190 p31776 p130191 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130195 :=
p130193 p130191 (nat_lit 1006259) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130194 (Eq.refl true))

noncomputable def p130196 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 2761089869)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130192 p31779 p130191 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130197 :=
@BSN.sin_arg_round false (nat_lit 1006259) (nat_lit 1048576) (nat_lit 97147213324416693829632)
  (nat_lit 75557863725914323419136) (nat_lit 2761089869) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130195 (p130196 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130198 :=
p130188 (nat_lit 1006259) (nat_lit 1048576) (nat_lit 24) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130189 BSN.pi_near_15 p130197 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130199 :=
@p130184 (nat_lit 257) (nat_lit 1048576) false (nat_lit 1006259) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130185 (nat_lit 250000000000000000) (nat_lit 82205511) (nat_lit 524288) (nat_lit 257)
    (nat_lit 1048576) p130187 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 82205511) (nat_lit 524288))
  (p130198 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130200 :=
@p130182 (nat_lit 1048576) (nat_lit 1006259) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 211027606185) (nat_lit 1099511627776) (nat_lit 175008708819) (nat_lit 3435973836800000)
  (@p32549 (nat_lit 209715) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32554
    (Eq.refl true))
  (@p130183 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 1006259) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p130199 (Eq.refl true))
    (Eq.refl true))

noncomputable def p130201 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 25))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1))))))
  (nat_lit 209715) (nat_lit 1048576)

noncomputable def p130202 :=
@p130201 (nat_lit 1) (nat_lit 1048576) (nat_lit 147439) (nat_lit 524288) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 30920169885) (nat_lit 549755813888) (nat_lit 86392821597) (nat_lit 1717986918400000)
  (@p32549 (nat_lit 209715) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32554
    (Eq.refl true))

noncomputable def p130203 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1)))))
  true (nat_lit 147439) (nat_lit 524288)

noncomputable def p130204 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1)))))
  true (nat_lit 294878) (nat_lit 1048576)

noncomputable def p130205 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 25) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 82205511)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 82205511) (nat_lit 524288)

noncomputable def p130206 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 82205511)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 97147213324416693829632))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130207 :=
nat_lit 2079968624780305128706441728291879689462046519401341819263916404434106894258721

noncomputable def p130208 :=
nat_lit 6233150112435134323429385792084877761462155965141046524918468552056536048603681

noncomputable def p130209 :=
BSN.cos_dyadic_bound_f (nat_lit 2761089869) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130207 p31681 p130191
  p130208 p31684

noncomputable def p130210 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 2761089869)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130207 p31681 p130191 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130211 :=
p130209 p130191 (nat_lit 294878) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130210 (Eq.refl true))

noncomputable def p130212 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 2761089869)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130208 p31684 p130191 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130213 :=
@BSN.cos_arg_round false (nat_lit 294878) (nat_lit 1048576) (nat_lit 97147213324416693829632)
  (nat_lit 75557863725914323419136) (nat_lit 2761089869) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130211 (p130212 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130214 :=
p130206 (nat_lit 294878) (nat_lit 1048576) (nat_lit 24) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130189 BSN.pi_near_15 p130213 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130215 :=
@p130205 (nat_lit 257) (nat_lit 1048576) true (nat_lit 294878) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130185 (nat_lit 250000000000000000) (nat_lit 82205511) (nat_lit 524288) (nat_lit 257)
    (nat_lit 1048576) p130187 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 82205511) (nat_lit 524288))
  (p130214 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130216 :=
p130202
  (@p130203 (nat_lit 819509) (nat_lit 3276800000)
    (@p130204 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 147439) (nat_lit 524288)
      (nat_lit 819509) (nat_lit 3276800000) (p130215 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130217 :=
@p130181 (nat_lit 211027606185) (nat_lit 1099511627776) (nat_lit 175008708819)
  (nat_lit 3435973836800000) false (nat_lit 30920169885) (nat_lit 549755813888) (nat_lit 86392821597)
  (nat_lit 1717986918400000) (p130200 (Eq.refl true)) p130216

noncomputable def p130218 :=
@p130177 false (nat_lit 28184961886012183674880) (nat_lit 25634073505) (nat_lit 274877906944)
  (nat_lit 824324141343) (nat_lit 429496729600000) d1198
  (p130180 p130217) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130219 :=
p130218 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130220 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 26)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1)))))) }

noncomputable def p130221 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 26)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130222 :=
@p130220 true (nat_lit 5886530875) (nat_lit 549755813888) (nat_lit 84031688773)
  (nat_lit 1717986918400000) true (nat_lit 215310483073) (nat_lit 1099511627776) (nat_lit 171156380671)
  (nat_lit 3435973836800000) p130221

noncomputable def p130223 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1)))))))
  true

noncomputable def p130224 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1)))))
  (nat_lit 205643) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130225 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1)))))
  true (nat_lit 57250) (nat_lit 1048576)

noncomputable def p130226 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 166414311)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 166414311) (nat_lit 1048576)

noncomputable def p130227 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1))))
  false (nat_lit 178686006445802150529) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p130228 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3668288609262839) (nat_lit 1125899906842624)

noncomputable def p130229 :=
@p130228 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 178686006445802150529)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 26) (nat_lit 1) (nat_lit 3668288609262839) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32608 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3668288609262839)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32613 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130230 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 166414311)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8254738449584317530112))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130231 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 166414311) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 25) (nat_lit 8254738449584317530112) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130232 :=
BSN.sin_dyadic_bound_f (nat_lit 117306888) (nat_lit 2147483648) (nat_lit 1) (nat_lit 0) (nat_lit 1048576)
  (nat_lit 400391) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1)

noncomputable def p130233 :=
p130232 (nat_lit 1) (nat_lit 57250) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.sinEvenP (nat_lit 117306888)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))

noncomputable def p130234 :=
p130233
  (@BSN.binarySplit_of_le (BSN.sinOddP (nat_lit 117306888)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130235 :=
@BSN.sin_arg_round false (nat_lit 57250) (nat_lit 1048576) (nat_lit 8254738449584317530112)
  (nat_lit 151115727451828646838272) (nat_lit 117306888) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  p130234 (Eq.refl true)

noncomputable def p130236 :=
p130230 (nat_lit 57250) (nat_lit 1048576) (nat_lit 25) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130231 BSN.pi_near_15 p130235 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130237 :=
@p130226 (nat_lit 1) (nat_lit 4096) true (nat_lit 57250) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130227 (nat_lit 250000000000000000) (nat_lit 166414311) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130229 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 166414311) (nat_lit 1048576))
  (p130236 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130238 :=
@p130224 (nat_lit 1048576) (nat_lit 28625) (nat_lit 524288) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 5886530875) (nat_lit 549755813888) (nat_lit 84031688773) (nat_lit 1717986918400000)
  (@p32598 (nat_lit 205643) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32603
    (Eq.refl true))
  (@p130225 (nat_lit 204096) (nat_lit 819200000) (nat_lit 28625) (nat_lit 524288) (nat_lit 3189)
    (nat_lit 12800000) (p130237 (Eq.refl true)) (Eq.refl true))

noncomputable def p130239 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 26))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1))))))
  (nat_lit 205643) (nat_lit 1048576)

noncomputable def p130240 :=
@p130239 (nat_lit 1) (nat_lit 1048576) (nat_lit 1047011) (nat_lit 1048576) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 215310483073) (nat_lit 1099511627776) (nat_lit 171156380671) (nat_lit 3435973836800000)
  (@p32598 (nat_lit 205643) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32603
    (Eq.refl true))

noncomputable def p130241 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1)))))
  false (nat_lit 1047011) (nat_lit 1048576)

noncomputable def p130242 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1)))))
  false (nat_lit 1047011) (nat_lit 1048576)

noncomputable def p130243 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 26) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 166414311)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 166414311) (nat_lit 1048576)

noncomputable def p130244 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 166414311)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 8254738449584317530112))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130245 :=
BSN.cos_dyadic_bound_f (nat_lit 117306888) (nat_lit 2147483648) (nat_lit 1) (nat_lit 0) (nat_lit 1048576)
  (nat_lit 400391) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1)

noncomputable def p130246 :=
p130245 (nat_lit 1) (nat_lit 1047011) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.cosEvenP (nat_lit 117306888)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))

noncomputable def p130247 :=
p130246
  (@BSN.binarySplit_of_le (BSN.cosOddP (nat_lit 117306888)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 0)
    (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130248 :=
@BSN.cos_arg_round false (nat_lit 1047011) (nat_lit 1048576) (nat_lit 8254738449584317530112)
  (nat_lit 151115727451828646838272) (nat_lit 117306888) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  p130247 (Eq.refl true)

noncomputable def p130249 :=
p130244 (nat_lit 1047011) (nat_lit 1048576) (nat_lit 25) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130231 BSN.pi_near_15 p130248 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130250 :=
@p130243 (nat_lit 1) (nat_lit 4096) false (nat_lit 1047011) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130227 (nat_lit 250000000000000000) (nat_lit 166414311) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130229 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 166414311) (nat_lit 1048576))
  (p130249 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130251 :=
p130240
  (@p130241 (nat_lit 3189) (nat_lit 12800000)
    (@p130242 (nat_lit 204096) (nat_lit 819200000) (nat_lit 1047011) (nat_lit 1048576) (nat_lit 3189)
      (nat_lit 12800000) (p130250 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130252 :=
@p130223 (nat_lit 5886530875) (nat_lit 549755813888) (nat_lit 84031688773) (nat_lit 1717986918400000)
  true (nat_lit 215310483073) (nat_lit 1099511627776) (nat_lit 171156380671) (nat_lit 3435973836800000)
  (p130238 (Eq.refl true)) p130251

noncomputable def p130253 :=
@p130173 true (nat_lit 30999133044195597484032) (nat_lit 112774189053) (nat_lit 1099511627776)
  (nat_lit 1353149902283) (nat_lit 687194767360000)
  (@p130174 (nat_lit 6610554996369) (nat_lit 3435973836800000) false (nat_lit 25634073505)
    (nat_lit 274877906944) (nat_lit 824324141343) (nat_lit 429496729600000)
    (p129097 (nat_lit 25) (nat_lit 26) (Eq.refl true) (Eq.refl true))
    (p130219 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (p130222 p130252)

noncomputable def p130254 :=
p130253 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130255 :=
p130254 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130256 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 27)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1)))))) }

noncomputable def p130257 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 27)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130258 :=
@p130256 true (nat_lit 200711505189) (nat_lit 1099511627776) (nat_lit 6739403023)
  (nat_lit 137438953472000) false (nat_lit 16751940387) (nat_lit 274877906944) (nat_lit 1664145787)
  (nat_lit 34359738368000) p130257

noncomputable def p130259 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1)))))))
  true

noncomputable def p130260 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1)))))
  (nat_lit 201799) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130261 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1)))))
  true (nat_lit 994611) (nat_lit 1048576)

noncomputable def p130262 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10521375)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  false (nat_lit 10521375) (nat_lit 65536)

noncomputable def p130263 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1))))
  false (nat_lit 36151169374234690893) (nat_lit 225179981368524800) (nat_lit 60888750048711)

noncomputable def p130264 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3710780868205815) (nat_lit 1125899906842624)

noncomputable def p130265 :=
@p130264 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 36151169374234690893)
  (nat_lit 225179981368524800) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 27) (nat_lit 1) (nat_lit 3710780868205815) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32658 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3710780868205815)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32663 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130266 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10521375)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3043248227129480970240))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9444732965739290427392)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130267 :=
BSN.sin_reduce_arg_pos_rat_q2 (nat_lit 10521375) (nat_lit 65536) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 25) (nat_lit 3043248227129480970240) (nat_lit 9444732965739290427392)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130268 :=
nat_lit 229250471454295486881281709074008336

noncomputable def p130269 :=
BSN.cos_dyadic_bound_f (nat_lit 691954534) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130268 p31541 p130268
  p130268 p31542

noncomputable def p130270 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 691954534)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130268 p31541 p130268 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130271 :=
p130269 p130268 (nat_lit 994611) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130270 (Eq.refl true))

noncomputable def p130272 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 691954534)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130268 p31542 p130268 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130273 :=
@BSN.cos_arg_round false (nat_lit 994611) (nat_lit 1048576) (nat_lit 3043248227129480970240)
  (nat_lit 9444732965739290427392) (nat_lit 691954534) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130271 (p130272 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130274 :=
p130266 (nat_lit 994611) (nat_lit 1048576) (nat_lit 25) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130267 BSN.pi_near_15 p130273 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130275 :=
@p130262 (nat_lit 257) (nat_lit 1048576) true (nat_lit 994611) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130263 (nat_lit 250000000000000000) (nat_lit 10521375) (nat_lit 65536) (nat_lit 257)
    (nat_lit 1048576) p130265 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 10521375) (nat_lit 65536))
  (p130274 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130276 :=
@p130260 (nat_lit 1048576) (nat_lit 994611) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 200711505189) (nat_lit 1099511627776) (nat_lit 6739403023) (nat_lit 137438953472000)
  (@p32648 (nat_lit 201799) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32653
    (Eq.refl true))
  (@p130261 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 994611) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p130275 (Eq.refl true))
    (Eq.refl true))

noncomputable def p130277 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 27))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1))))))
  (nat_lit 201799) (nat_lit 1048576)

noncomputable def p130278 :=
@p130277 (nat_lit 1) (nat_lit 1048576) (nat_lit 83013) (nat_lit 262144) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 16751940387) (nat_lit 274877906944) (nat_lit 1664145787) (nat_lit 34359738368000)
  (@p32648 (nat_lit 201799) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32653
    (Eq.refl true))

noncomputable def p130279 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1)))))
  true (nat_lit 83013) (nat_lit 262144)

noncomputable def p130280 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1)))))
  true (nat_lit 332052) (nat_lit 1048576)

noncomputable def p130281 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 27) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10521375)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  false (nat_lit 10521375) (nat_lit 65536)

noncomputable def p130282 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 10521375)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 3043248227129480970240))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9444732965739290427392)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130283 :=
BSN.sin_dyadic_bound_f (nat_lit 691954534) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130268 p31525 p130268
  p130268 p31526

noncomputable def p130284 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 691954534)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130268 p31525 p130268 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130285 :=
p130283 p130268 (nat_lit 332052) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130284 (Eq.refl true))

noncomputable def p130286 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 691954534)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130268 p31526 p130268 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130287 :=
@BSN.sin_arg_round false (nat_lit 332052) (nat_lit 1048576) (nat_lit 3043248227129480970240)
  (nat_lit 9444732965739290427392) (nat_lit 691954534) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130285 (p130286 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130288 :=
p130282 (nat_lit 332052) (nat_lit 1048576) (nat_lit 25) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130267 BSN.pi_near_15 p130287 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130289 :=
@p130281 (nat_lit 257) (nat_lit 1048576) true (nat_lit 332052) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130263 (nat_lit 250000000000000000) (nat_lit 10521375) (nat_lit 65536) (nat_lit 257)
    (nat_lit 1048576) p130265 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 10521375) (nat_lit 65536))
  (p130288 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130290 :=
p130278
  (@p130279 (nat_lit 819509) (nat_lit 3276800000)
    (@p130280 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 83013) (nat_lit 262144)
      (nat_lit 819509) (nat_lit 3276800000) (p130289 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130291 :=
@p130259 (nat_lit 200711505189) (nat_lit 1099511627776) (nat_lit 6739403023) (nat_lit 137438953472000)
  false (nat_lit 16751940387) (nat_lit 274877906944) (nat_lit 1664145787) (nat_lit 34359738368000)
  (p130276 (Eq.refl true)) p130290

noncomputable def p130292 :=
@p130169 true (nat_lit 12580179800878712094720) (nat_lit 45766427505) (nat_lit 1099511627776)
  (nat_lit 1386432818023) (nat_lit 687194767360000)
  (@p130170 (nat_lit 1355723674783) (nat_lit 687194767360000) true (nat_lit 112774189053)
    (nat_lit 1099511627776) (nat_lit 1353149902283) (nat_lit 687194767360000)
    (p129097 (nat_lit 26) (nat_lit 27) (Eq.refl true) (Eq.refl true))
    p130255)
  (p130258 p130291)

noncomputable def p130293 :=
p130292 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130294 :=
p130293 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130295 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 28)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1)))))) }

noncomputable def p130296 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 28)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130297 :=
@p130295 false (nat_lit 103771027395) (nat_lit 1099511627776) (nat_lit 164033634601)
  (nat_lit 3435973836800000) false (nat_lit 45005393419) (nat_lit 274877906944) (nat_lit 20654511747)
  (nat_lit 429496729600000) p130296

noncomputable def p130298 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1)))))))
  false

noncomputable def p130299 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1)))))
  (nat_lit 198163) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130300 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1)))))
  false (nat_lit 523665) (nat_lit 1048576)

noncomputable def p130301 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 170199545)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 170199545) (nat_lit 1048576)

noncomputable def p130302 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1))))
  false (nat_lit 182750370921840794241) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p130303 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3751726938922231) (nat_lit 1125899906842624)

noncomputable def p130304 :=
@p130303 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 182750370921840794241)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 28) (nat_lit 1) (nat_lit 3751726938922231) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32709 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3751726938922231)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32714 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130305 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 170199545)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 79020389066166239232000))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130306 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 170199545) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 25) (nat_lit 79020389066166239232000) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130307 :=
nat_lit 1590147649350905496114133183446302976

noncomputable def p130308 :=
BSN.sin_dyadic_bound_f (nat_lit 1122947268) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130307 p31525 p130307
  p130307 p31526

noncomputable def p130309 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1122947268)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130307 p31525 p130307 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130310 :=
p130308 p130307 (nat_lit 523665) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130309 (Eq.refl true))

noncomputable def p130311 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1122947268)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130307 p31526 p130307 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130312 :=
@BSN.sin_arg_round false (nat_lit 523665) (nat_lit 1048576) (nat_lit 79020389066166239232000)
  (nat_lit 151115727451828646838272) (nat_lit 1122947268) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130310 (p130311 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130313 :=
p130305 (nat_lit 523665) (nat_lit 1048576) (nat_lit 25) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130306 BSN.pi_near_15 p130312 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130314 :=
@p130301 (nat_lit 257) (nat_lit 1048576) false (nat_lit 523665) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130302 (nat_lit 250000000000000000) (nat_lit 170199545) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p130304 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 170199545) (nat_lit 1048576))
  (p130313 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130315 :=
@p130299 (nat_lit 1048576) (nat_lit 523665) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 103771027395) (nat_lit 1099511627776) (nat_lit 164033634601) (nat_lit 3435973836800000)
  (@p32699 (nat_lit 198163) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32704
    (Eq.refl true))
  (@p130300 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 523665) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p130314 (Eq.refl true))
    (Eq.refl true))

noncomputable def p130316 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 28))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1))))))
  (nat_lit 198163) (nat_lit 1048576)

noncomputable def p130317 :=
@p130316 (nat_lit 1) (nat_lit 1048576) (nat_lit 227113) (nat_lit 262144) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 45005393419) (nat_lit 274877906944) (nat_lit 20654511747) (nat_lit 429496729600000)
  (@p32699 (nat_lit 198163) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32704
    (Eq.refl true))

noncomputable def p130318 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1)))))
  true (nat_lit 227113) (nat_lit 262144)

noncomputable def p130319 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1)))))
  true (nat_lit 908452) (nat_lit 1048576)

noncomputable def p130320 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 28) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 170199545)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 170199545) (nat_lit 1048576)

noncomputable def p130321 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 170199545)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 79020389066166239232000))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130322 :=
BSN.cos_dyadic_bound_f (nat_lit 1122947268) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130307 p31541 p130307
  p130307 p31542

noncomputable def p130323 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 1122947268)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130307 p31541 p130307 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130324 :=
p130322 p130307 (nat_lit 908452) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130323 (Eq.refl true))

noncomputable def p130325 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 1122947268)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130307 p31542 p130307 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130326 :=
@BSN.cos_arg_round false (nat_lit 908452) (nat_lit 1048576) (nat_lit 79020389066166239232000)
  (nat_lit 151115727451828646838272) (nat_lit 1122947268) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130324 (p130325 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130327 :=
p130321 (nat_lit 908452) (nat_lit 1048576) (nat_lit 25) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130306 BSN.pi_near_15 p130326 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130328 :=
@p130320 (nat_lit 257) (nat_lit 1048576) true (nat_lit 908452) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130302 (nat_lit 250000000000000000) (nat_lit 170199545) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p130304 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 170199545) (nat_lit 1048576))
  (p130327 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130329 :=
p130317
  (@p130318 (nat_lit 819509) (nat_lit 3276800000)
    (@p130319 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 227113) (nat_lit 262144)
      (nat_lit 819509) (nat_lit 3276800000) (p130328 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130330 :=
@p130298 (nat_lit 103771027395) (nat_lit 1099511627776) (nat_lit 164033634601)
  (nat_lit 3435973836800000) false (nat_lit 45005393419) (nat_lit 274877906944) (nat_lit 20654511747)
  (nat_lit 429496729600000) (p130315 (Eq.refl true)) p130329

noncomputable def p130331 :=
@p130165 false (nat_lit 36903773575945255911424) (nat_lit 134255146171) (nat_lit 1099511627776)
  (nat_lit 7097400184091) (nat_lit 3435973836800000)
  (@p130166 (nat_lit 694710344949) (nat_lit 343597383680000) true (nat_lit 45766427505)
    (nat_lit 1099511627776) (nat_lit 1386432818023) (nat_lit 687194767360000)
    (p129097 (nat_lit 27) (nat_lit 28) (Eq.refl true) (Eq.refl true))
    p130294)
  (p130297 p130330)

noncomputable def p130332 :=
p130331 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130333 :=
p130332 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130334 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 29)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1)))))) }

noncomputable def p130335 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 29)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130336 :=
@p130334 false (nat_lit 161113227165) (nat_lit 1099511627776) (nat_lit 162157236319)
  (nat_lit 3435973836800000) true (nat_lit 125416515645) (nat_lit 1099511627776) (nat_lit 161584336319)
  (nat_lit 3435973836800000) p130335

noncomputable def p130337 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1)))))))
  false

noncomputable def p130338 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1)))))
  (nat_lit 194715) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130339 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1)))))
  false (nat_lit 827431) (nat_lit 1048576)

noncomputable def p130340 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 171991915)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 171991915) (nat_lit 1048576)

noncomputable def p130341 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1))))
  false (nat_lit 36934982701535806797) (nat_lit 225179981368524800) (nat_lit 60888750048711)

noncomputable def p130342 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3791236343078135) (nat_lit 1125899906842624)

noncomputable def p130343 :=
@p130342 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 36934982701535806797)
  (nat_lit 225179981368524800) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 29) (nat_lit 1) (nat_lit 3791236343078135) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32760 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3791236343078135)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32764 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130344 :=
BSN.cos_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 171991915)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 99956099115416876482560))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130345 :=
BSN.sin_reduce_arg_pos_rat_q0 (nat_lit 171991915) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 26) (nat_lit 99956099115416876482560) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130346 :=
nat_lit 145477630783159040412148946939103528535943604395797115652227502298504199700736

noncomputable def p130347 :=
nat_lit 16574330199321140857495484170568756305870520156953574354787168121796198656

noncomputable def p130348 :=
nat_lit 436399743689078478954731849848969448095219072147077439807972932559269006704896

noncomputable def p130349 :=
BSN.cos_dyadic_bound_f (nat_lit 1420461602) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130346 p31681 p130347
  p130348 p31684

noncomputable def p130350 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1420461602)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130346 p31681 p130347 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130351 :=
p130349 p130347 (nat_lit 827431) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130350 (Eq.refl true))

noncomputable def p130352 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1420461602)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130348 p31684 p130347 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130353 :=
@BSN.cos_arg_round false (nat_lit 827431) (nat_lit 1048576) (nat_lit 99956099115416876482560)
  (nat_lit 151115727451828646838272) (nat_lit 1420461602) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130351 (p130352 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130354 :=
p130344 (nat_lit 827431) (nat_lit 1048576) (nat_lit 26) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130345 BSN.pi_near_15 p130353 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130355 :=
@p130340 (nat_lit 257) (nat_lit 1048576) false (nat_lit 827431) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130341 (nat_lit 250000000000000000) (nat_lit 171991915) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p130343 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 171991915) (nat_lit 1048576))
  (p130354 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130356 :=
@p130338 (nat_lit 1048576) (nat_lit 827431) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 161113227165) (nat_lit 1099511627776) (nat_lit 162157236319) (nat_lit 3435973836800000)
  (@p32750 (nat_lit 194715) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32755
    (Eq.refl true))
  (@p130339 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 827431) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p130355 (Eq.refl true))
    (Eq.refl true))

noncomputable def p130357 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1))))))
  (nat_lit 194715) (nat_lit 1048576)

noncomputable def p130358 :=
@p130357 (nat_lit 1) (nat_lit 1048576) (nat_lit 644103) (nat_lit 1048576) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 125416515645) (nat_lit 1099511627776) (nat_lit 161584336319) (nat_lit 3435973836800000)
  (@p32750 (nat_lit 194715) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32755
    (Eq.refl true))

noncomputable def p130359 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1)))))
  false (nat_lit 644103) (nat_lit 1048576)

noncomputable def p130360 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1)))))
  false (nat_lit 644103) (nat_lit 1048576)

noncomputable def p130361 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 29) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 171991915)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 171991915) (nat_lit 1048576)

noncomputable def p130362 :=
BSN.sin_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 171991915)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 99956099115416876482560))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130363 :=
nat_lit 4071158336311809533290313544012211216

noncomputable def p130364 :=
BSN.sin_dyadic_bound_f (nat_lit 1420461602) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130363 p31525 p130363
  p130363 p31526

noncomputable def p130365 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1420461602)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130363 p31525 p130363 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130366 :=
p130364 p130363 (nat_lit 644103) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130365 (Eq.refl true))

noncomputable def p130367 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1420461602)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130363 p31526 p130363 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130368 :=
@BSN.sin_arg_round false (nat_lit 644103) (nat_lit 1048576) (nat_lit 99956099115416876482560)
  (nat_lit 151115727451828646838272) (nat_lit 1420461602) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130366 (p130367 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130369 :=
p130362 (nat_lit 644103) (nat_lit 1048576) (nat_lit 26) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130345 BSN.pi_near_15 p130368 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130370 :=
@p130361 (nat_lit 257) (nat_lit 1048576) false (nat_lit 644103) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130341 (nat_lit 250000000000000000) (nat_lit 171991915) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p130343 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 171991915) (nat_lit 1048576))
  (p130369 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130371 :=
p130358
  (@p130359 (nat_lit 819509) (nat_lit 3276800000)
    (@p130360 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 644103) (nat_lit 1048576)
      (nat_lit 819509) (nat_lit 3276800000) (p130370 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130372 :=
@p130337 (nat_lit 161113227165) (nat_lit 1099511627776) (nat_lit 162157236319)
  (nat_lit 3435973836800000) true (nat_lit 125416515645) (nat_lit 1099511627776) (nat_lit 161584336319)
  (nat_lit 3435973836800000) (p130356 (Eq.refl true)) p130371

noncomputable def p130373 :=
@p130161 false (nat_lit 9718177036952903090176) (nat_lit 4419315263) (nat_lit 549755813888)
  (nat_lit 725898452041) (nat_lit 343597383680000)
  (@p130162 (nat_lit 7111137084091) (nat_lit 3435973836800000) false (nat_lit 134255146171)
    (nat_lit 1099511627776) (nat_lit 7097400184091) (nat_lit 3435973836800000)
    (p129097 (nat_lit 28) (nat_lit 29) (Eq.refl true) (Eq.refl true))
    p130333)
  (p130336 p130372)

noncomputable def p130374 :=
p130373 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130375 :=
p130374 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130376 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 30)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1)))))) }

noncomputable def p130377 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 30)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130378 :=
@p130376 true (nat_lit 33914318893) (nat_lit 274877906944) (nat_lit 39626551499)
  (nat_lit 858993459200000) true (nat_lit 73984104565) (nat_lit 549755813888) (nat_lit 79353581123)
  (nat_lit 1717986918400000) p130377

noncomputable def p130379 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1)))))))
  true

noncomputable def p130380 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1)))))
  (nat_lit 191443) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130381 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1)))))
  true (nat_lit 708604) (nat_lit 1048576)

noncomputable def p130382 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 86861747)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 86861747) (nat_lit 524288)

noncomputable def p130383 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1))))
  false (nat_lit 186534181902107171457) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p130384 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3829405717437687) (nat_lit 1125899906842624)

noncomputable def p130385 :=
@p130384 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 186534181902107171457)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 30) (nat_lit 1) (nat_lit 3829405717437687) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32810 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3829405717437687)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32815 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130386 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 86861747)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 56065451383174079709184))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130387 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 86861747) (nat_lit 524288) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 26) (nat_lit 56065451383174079709184) (nat_lit 75557863725914323419136)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130388 :=
nat_lit 6447362251937413258911077878858776576

noncomputable def p130389 :=
BSN.sin_dyadic_bound_f (nat_lit 1593475968) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130388 p31525 p130388
  p130388 p31526

noncomputable def p130390 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1593475968)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130388 p31525 p130388 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130391 :=
p130389 p130388 (nat_lit 708604) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130390 (Eq.refl true))

noncomputable def p130392 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1593475968)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130388 p31526 p130388 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130393 :=
@BSN.sin_arg_round false (nat_lit 708604) (nat_lit 1048576) (nat_lit 56065451383174079709184)
  (nat_lit 75557863725914323419136) (nat_lit 1593475968) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130391 (p130392 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130394 :=
p130386 (nat_lit 708604) (nat_lit 1048576) (nat_lit 26) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130387 BSN.pi_near_15 p130393 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130395 :=
@p130382 (nat_lit 1) (nat_lit 4096) true (nat_lit 708604) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130383 (nat_lit 250000000000000000) (nat_lit 86861747) (nat_lit 524288) (nat_lit 1)
    (nat_lit 4096) p130385 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 86861747) (nat_lit 524288))
  (p130394 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130396 :=
@p130380 (nat_lit 1048576) (nat_lit 177151) (nat_lit 262144) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 33914318893) (nat_lit 274877906944) (nat_lit 39626551499) (nat_lit 858993459200000)
  (@p32800 (nat_lit 191443) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32805
    (Eq.refl true))
  (@p130381 (nat_lit 204096) (nat_lit 819200000) (nat_lit 177151) (nat_lit 262144) (nat_lit 3189)
    (nat_lit 12800000) (p130395 (Eq.refl true)) (Eq.refl true))

noncomputable def p130397 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 30))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1))))))
  (nat_lit 191443) (nat_lit 1048576)

noncomputable def p130398 :=
@p130397 (nat_lit 1) (nat_lit 1048576) (nat_lit 386455) (nat_lit 524288) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 73984104565) (nat_lit 549755813888) (nat_lit 79353581123) (nat_lit 1717986918400000)
  (@p32800 (nat_lit 191443) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32805
    (Eq.refl true))

noncomputable def p130399 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1)))))
  false (nat_lit 386455) (nat_lit 524288)

noncomputable def p130400 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1)))))
  false (nat_lit 772910) (nat_lit 1048576)

noncomputable def p130401 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 30) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 86861747)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 86861747) (nat_lit 524288)

noncomputable def p130402 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 86861747)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 56065451383174079709184))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130403 :=
nat_lit 230403555666035077574788865921881298727247233084135165738784325874585390022656

noncomputable def p130404 :=
nat_lit 41568480007707472720059089381732741642546398197350296781813868663486283776

noncomputable def p130405 :=
nat_lit 691127530038089817778926479586880430698456606456010796622789349886429197500416

noncomputable def p130406 :=
BSN.cos_dyadic_bound_f (nat_lit 1593475968) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130403 p31681 p130404
  p130405 p31684

noncomputable def p130407 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1593475968)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130403 p31681 p130404 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130408 :=
p130406 p130404 (nat_lit 772910) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130407 (Eq.refl true))

noncomputable def p130409 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1593475968)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130405 p31684 p130404 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130410 :=
@BSN.cos_arg_round false (nat_lit 772910) (nat_lit 1048576) (nat_lit 56065451383174079709184)
  (nat_lit 75557863725914323419136) (nat_lit 1593475968) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130408 (p130409 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130411 :=
p130402 (nat_lit 772910) (nat_lit 1048576) (nat_lit 26) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130387 BSN.pi_near_15 p130410 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130412 :=
@p130401 (nat_lit 1) (nat_lit 4096) false (nat_lit 772910) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130383 (nat_lit 250000000000000000) (nat_lit 86861747) (nat_lit 524288) (nat_lit 1)
    (nat_lit 4096) p130385 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 86861747) (nat_lit 524288))
  (p130411 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130413 :=
p130398
  (@p130399 (nat_lit 3189) (nat_lit 12800000)
    (@p130400 (nat_lit 204096) (nat_lit 819200000) (nat_lit 386455) (nat_lit 524288) (nat_lit 3189)
      (nat_lit 12800000) (p130412 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130414 :=
@p130379 (nat_lit 33914318893) (nat_lit 274877906944) (nat_lit 39626551499) (nat_lit 858993459200000)
  true (nat_lit 73984104565) (nat_lit 549755813888) (nat_lit 79353581123) (nat_lit 1717986918400000)
  (p130396 (Eq.refl true)) p130413

noncomputable def p130415 :=
@p130157 true (nat_lit 38243647360668245426176) (nat_lit 34782394651) (nat_lit 274877906944)
  (nat_lit 231802865083) (nat_lit 107374182400000)
  (@p130158 (nat_lit 727329432041) (nat_lit 343597383680000) false (nat_lit 4419315263)
    (nat_lit 549755813888) (nat_lit 725898452041) (nat_lit 343597383680000)
    (p129097 (nat_lit 29) (nat_lit 30) (Eq.refl true) (Eq.refl true))
    p130375)
  (p130378 p130414)

noncomputable def p130416 :=
p130415 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130417 :=
p130416 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130418 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 31)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1)))))) }

noncomputable def p130419 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 31)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130420 :=
@p130418 true (nat_lit 35493801643) (nat_lit 274877906944) (nat_lit 7805271811)
  (nat_lit 171798691840000) false (nat_lit 68629912535) (nat_lit 549755813888) (nat_lit 15602719247)
  (nat_lit 343597383680000) p130419

noncomputable def p130421 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1)))))))
  true

noncomputable def p130422 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1)))))
  (nat_lit 188329) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130423 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1)))))
  true (nat_lit 753868) (nat_lit 1048576)

noncomputable def p130424 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 175398373)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 175398373) (nat_lit 1048576)

noncomputable def p130425 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1))))
  false (nat_lit 188332569560316271233) (nat_lit 1125899906842624000) (nat_lit 60888750048711)

noncomputable def p130426 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 3866325256314103) (nat_lit 1125899906842624)

noncomputable def p130427 :=
@p130426 (nat_lit 1250000001) (nat_lit 250000000000000) (nat_lit 188332569560316271233)
  (nat_lit 1125899906842624000) (nat_lit 60888750048711) (nat_lit 250000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 31) (nat_lit 1) (nat_lit 3866325256314103) (nat_lit 1125899906842624)
    (nat_lit 1250000001) (nat_lit 250000000000000) false
    (@p32861 (nat_lit 1000000000800000) (nat_lit 200000000000000000000) (nat_lit 3866325256314103)
      (nat_lit 1125899906842624) (nat_lit 1250000001) (nat_lit 250000000000000)
      (p32866 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130428 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 175398373)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 116134375253378414411776))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130429 :=
BSN.sin_reduce_arg_pos_rat_q2 (nat_lit 175398373) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 26) (nat_lit 116134375253378414411776) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130430 :=
nat_lit 265120223936212115882805440427515227551621973417971091052773930840713319710976

noncomputable def p130431 :=
nat_lit 55036131437773228360100130414599146212997054433196276313088187642999767296

noncomputable def p130432 :=
nat_lit 795250599545760801191696121021716484362439926145046880605695616146853959598336

noncomputable def p130433 :=
BSN.cos_dyadic_bound_f (nat_lit 1650368734) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130430 p31681 p130431
  p130432 p31684

noncomputable def p130434 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1650368734)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130430 p31681 p130431 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130435 :=
p130433 p130431 (nat_lit 753868) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130434 (Eq.refl true))

noncomputable def p130436 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1650368734)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130432 p31684 p130431 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130437 :=
@BSN.cos_arg_round false (nat_lit 753868) (nat_lit 1048576) (nat_lit 116134375253378414411776)
  (nat_lit 151115727451828646838272) (nat_lit 1650368734) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130435 (p130436 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130438 :=
p130428 (nat_lit 753868) (nat_lit 1048576) (nat_lit 26) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130429 BSN.pi_near_15 p130437 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130439 :=
@p130424 (nat_lit 1) (nat_lit 4096) true (nat_lit 753868) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130425 (nat_lit 250000000000000000) (nat_lit 175398373) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130427 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 175398373) (nat_lit 1048576))
  (p130438 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130440 :=
@p130422 (nat_lit 1048576) (nat_lit 188467) (nat_lit 262144) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 35493801643) (nat_lit 274877906944) (nat_lit 7805271811) (nat_lit 171798691840000)
  (@p32851 (nat_lit 188329) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32856
    (Eq.refl true))
  (@p130423 (nat_lit 204096) (nat_lit 819200000) (nat_lit 188467) (nat_lit 262144) (nat_lit 3189)
    (nat_lit 12800000) (p130439 (Eq.refl true)) (Eq.refl true))

noncomputable def p130441 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 31))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1))))))
  (nat_lit 188329) (nat_lit 1048576)

noncomputable def p130442 :=
@p130441 (nat_lit 1) (nat_lit 1048576) (nat_lit 364415) (nat_lit 524288) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 68629912535) (nat_lit 549755813888) (nat_lit 15602719247) (nat_lit 343597383680000)
  (@p32851 (nat_lit 188329) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32856
    (Eq.refl true))

noncomputable def p130443 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1)))))
  true (nat_lit 364415) (nat_lit 524288)

noncomputable def p130444 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1)))))
  true (nat_lit 728830) (nat_lit 1048576)

noncomputable def p130445 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 31) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 175398373)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 175398373) (nat_lit 1048576)

noncomputable def p130446 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 175398373)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 116134375253378414411776))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130447 :=
nat_lit 7418634068194307989155179261764715536

noncomputable def p130448 :=
BSN.sin_dyadic_bound_f (nat_lit 1650368734) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130447 p31525 p130447
  p130447 p31526

noncomputable def p130449 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1650368734)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130447 p31525 p130447 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130450 :=
p130448 p130447 (nat_lit 728830) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130449 (Eq.refl true))

noncomputable def p130451 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1650368734)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130447 p31526 p130447 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130452 :=
@BSN.sin_arg_round false (nat_lit 728830) (nat_lit 1048576) (nat_lit 116134375253378414411776)
  (nat_lit 151115727451828646838272) (nat_lit 1650368734) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130450 (p130451 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130453 :=
p130446 (nat_lit 728830) (nat_lit 1048576) (nat_lit 26) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130429 BSN.pi_near_15 p130452 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130454 :=
@p130445 (nat_lit 1) (nat_lit 4096) true (nat_lit 728830) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130425 (nat_lit 250000000000000000) (nat_lit 175398373) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130427 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 175398373) (nat_lit 1048576))
  (p130453 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130455 :=
p130442
  (@p130443 (nat_lit 3189) (nat_lit 12800000)
    (@p130444 (nat_lit 204096) (nat_lit 819200000) (nat_lit 364415) (nat_lit 524288) (nat_lit 3189)
      (nat_lit 12800000) (p130454 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130456 :=
@p130421 (nat_lit 35493801643) (nat_lit 274877906944) (nat_lit 7805271811) (nat_lit 171798691840000)
  false (nat_lit 68629912535) (nat_lit 549755813888) (nat_lit 15602719247) (nat_lit 343597383680000)
  (p130440 (Eq.refl true)) p130455

noncomputable def p130457 :=
@p130153 true (nat_lit 256976968963533570048) (nat_lit 934876767) (nat_lit 549755813888)
  (nat_lit 3786859437563) (nat_lit 1717986918400000)
  (@p130154 (nat_lit 3715900263203) (nat_lit 1717986918400000) true (nat_lit 34782394651)
    (nat_lit 274877906944) (nat_lit 231802865083) (nat_lit 107374182400000)
    (p129097 (nat_lit 30) (nat_lit 31) (Eq.refl true) (Eq.refl true))
    p130417)
  (p130420 p130456)

noncomputable def p130458 :=
p130457 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130459 :=
p130458 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130460 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 32)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1)))))) }

noncomputable def p130461 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 32)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130462 :=
@p130460 false (nat_lit 131668714427) (nat_lit 1099511627776) (nat_lit 154127244401)
  (nat_lit 3435973836800000) false (nat_lit 142975115975) (nat_lit 1099511627776) (nat_lit 154317856901)
  (nat_lit 3435973836800000) p130461

noncomputable def p130463 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1)))))))
  false

noncomputable def p130464 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1)))))
  (nat_lit 185363) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130465 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1)))))
  false (nat_lit 710329) (nat_lit 1048576)

noncomputable def p130466 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 177020035)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 177020035) (nat_lit 1048576)

noncomputable def p130467 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1))))
  false (nat_lit 152059052836051376769) (nat_lit 900719925474099200) (nat_lit 48711000048711)

noncomputable def p130468 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 15608286920413395) (nat_lit 4503599627370496)

noncomputable def p130469 :=
@p130468 (nat_lit 1000000001) (nat_lit 200000000000000) (nat_lit 152059052836051376769)
  (nat_lit 900719925474099200) (nat_lit 48711000048711) (nat_lit 200000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 32) (nat_lit 1) (nat_lit 15608286920413395) (nat_lit 4503599627370496)
    (nat_lit 1000000001) (nat_lit 200000000000000) false
    (@p32912 (nat_lit 1000000001000000) (nat_lit 200000000000000000000) (nat_lit 15608286920413395)
      (nat_lit 4503599627370496) (nat_lit 1000000001) (nat_lit 200000000000000)
      (p32917 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130470 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 177020035)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 112468469776575847464960))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130471 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 177020035) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 26) (nat_lit 112468469776575847464960) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130472 :=
nat_lit 6525351982493466626453360270994555136

noncomputable def p130473 :=
BSN.sin_dyadic_bound_f (nat_lit 1598273084) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130472 p31525 p130472
  p130472 p31526

noncomputable def p130474 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1598273084)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130472 p31525 p130472 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130475 :=
p130473 p130472 (nat_lit 710329) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130474 (Eq.refl true))

noncomputable def p130476 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1598273084)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130472 p31526 p130472 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130477 :=
@BSN.sin_arg_round false (nat_lit 710329) (nat_lit 1048576) (nat_lit 112468469776575847464960)
  (nat_lit 151115727451828646838272) (nat_lit 1598273084) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130475 (p130476 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130478 :=
p130470 (nat_lit 710329) (nat_lit 1048576) (nat_lit 26) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130471 BSN.pi_near_15 p130477 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130479 :=
@p130466 (nat_lit 257) (nat_lit 1048576) false (nat_lit 710329) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130467 (nat_lit 200000000000000000) (nat_lit 177020035) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p130469 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 177020035) (nat_lit 1048576))
  (p130478 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130480 :=
@p130464 (nat_lit 1048576) (nat_lit 710329) (nat_lit 1048576) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 131668714427) (nat_lit 1099511627776) (nat_lit 154127244401) (nat_lit 3435973836800000)
  (@p32902 (nat_lit 185363) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32907
    (Eq.refl true))
  (@p130465 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 710329) (nat_lit 1048576)
    (nat_lit 819509) (nat_lit 3276800000) (p130479 (Eq.refl true))
    (Eq.refl true))

noncomputable def p130481 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 32))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1))))))
  (nat_lit 185363) (nat_lit 1048576)

noncomputable def p130482 :=
@p130481 (nat_lit 1) (nat_lit 1048576) (nat_lit 771325) (nat_lit 1048576) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 142975115975) (nat_lit 1099511627776) (nat_lit 154317856901) (nat_lit 3435973836800000)
  (@p32902 (nat_lit 185363) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p32907
    (Eq.refl true))

noncomputable def p130483 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1)))))
  true (nat_lit 771325) (nat_lit 1048576)

noncomputable def p130484 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1)))))
  true (nat_lit 771325) (nat_lit 1048576)

noncomputable def p130485 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 32) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 177020035)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 177020035) (nat_lit 1048576)

noncomputable def p130486 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 177020035)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 112468469776575847464960))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130487 :=
nat_lit 233191113065982509723396840313952388063706788736059993818440563058793921970176

noncomputable def p130488 :=
nat_lit 42580218495431415182200085461212015138597552213982038742962833358543978496

noncomputable def p130489 :=
nat_lit 699488178760956666339826120770934740160843171103752017377835763509664677953536

noncomputable def p130490 :=
BSN.cos_dyadic_bound_f (nat_lit 1598273084) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130487 p31681 p130488
  p130489 p31684

noncomputable def p130491 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1598273084)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130487 p31681 p130488 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130492 :=
p130490 p130488 (nat_lit 771325) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130491 (Eq.refl true))

noncomputable def p130493 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1598273084)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130489 p31684 p130488 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130494 :=
@BSN.cos_arg_round false (nat_lit 771325) (nat_lit 1048576) (nat_lit 112468469776575847464960)
  (nat_lit 151115727451828646838272) (nat_lit 1598273084) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130492 (p130493 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130495 :=
p130486 (nat_lit 771325) (nat_lit 1048576) (nat_lit 26) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130471 BSN.pi_near_15 p130494 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130496 :=
@p130485 (nat_lit 257) (nat_lit 1048576) true (nat_lit 771325) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130467 (nat_lit 200000000000000000) (nat_lit 177020035) (nat_lit 1048576) (nat_lit 257)
    (nat_lit 1048576) p130469 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 177020035) (nat_lit 1048576))
  (p130495 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130497 :=
p130482
  (@p130483 (nat_lit 819509) (nat_lit 3276800000)
    (@p130484 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 771325) (nat_lit 1048576)
      (nat_lit 819509) (nat_lit 3276800000) (p130496 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130498 :=
@p130463 (nat_lit 131668714427) (nat_lit 1099511627776) (nat_lit 154127244401)
  (nat_lit 3435973836800000) false (nat_lit 142975115975) (nat_lit 1099511627776) (nat_lit 154317856901)
  (nat_lit 3435973836800000) (p130480 (Eq.refl true)) p130497

noncomputable def p130499 :=
@p130149 false (nat_lit 77573493372713181380608) (nat_lit 141105362441) (nat_lit 1099511627776)
  (nat_lit 7728036732027) (nat_lit 3435973836800000)
  (@p130150 (nat_lit 3793952981313) (nat_lit 1717986918400000) true (nat_lit 934876767)
    (nat_lit 549755813888) (nat_lit 3786859437563) (nat_lit 1717986918400000)
    (p129097 (nat_lit 31) (nat_lit 32) (Eq.refl true) (Eq.refl true))
    p130459)
  (p130462 p130498)

noncomputable def p130500 :=
p130499 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130501 :=
p130500 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d1199 : p130145 (nat_lit 3435973836800000) :=
@p130146 (nat_lit 7742033207027) (nat_lit 3435973836800000) false (nat_lit 141105362441)
  (nat_lit 1099511627776) (nat_lit 7728036732027) (nat_lit 3435973836800000)
  (p129097 (nat_lit 32) (nat_lit 33) (Eq.refl true) (Eq.refl true))
  p130501

noncomputable def p130502 :=
Enclosure.Complex.IsNear (p129093 (nat_lit 41)) false (nat_lit 612813288183)
  (nat_lit 1099511627776) (nat_lit 1779186709967) (nat_lit 687194767360000) true (nat_lit 50694497679)
  (nat_lit 1099511627776) (nat_lit 1776139299967)

noncomputable def p130503 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 41))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 40))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 40)) p129095))
  false (nat_lit 612813288183) (nat_lit 1099511627776)

noncomputable def p130504 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 40))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 40)) p129095)
  false (nat_lit 754488431583) (nat_lit 1099511627776) (nat_lit 8757391860671)

noncomputable def p130505 :=
@p130504 (nat_lit 3435973836800000) true (nat_lit 75724474077) (nat_lit 549755813888)
  (nat_lit 4371463053773) (nat_lit 1717986918400000) true (nat_lit 17709392925) (nat_lit 137438953472)
  (nat_lit 34635422291) (nat_lit 858993459200000)

noncomputable def p130506 :=
@p130505 false (nat_lit 100754450475) (nat_lit 1099511627776) (nat_lit 137770392289)
  (nat_lit 3435973836800000) false (nat_lit 84224417001606664421376) (nat_lit 612813288183) (nat_lit 1099511627776)
  (nat_lit 1779186709967) (nat_lit 687194767360000)

noncomputable def p130507 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 40))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 39))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 39)) p129095))
  false (nat_lit 754488431583) (nat_lit 1099511627776)

noncomputable def p130508 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 39))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 39)) p129095)
  false (nat_lit 449141405517) (nat_lit 549755813888) (nat_lit 4308819113937)

noncomputable def p130509 :=
@p130508 (nat_lit 1717986918400000) true (nat_lit 49854635013) (nat_lit 1099511627776)
  (nat_lit 8603957880999) (nat_lit 3435973836800000) true (nat_lit 143794379451) (nat_lit 1099511627776)
  (nat_lit 139753632797) (nat_lit 3435973836800000)

noncomputable def p130510 :=
@p130509 true (nat_lit 101594313141) (nat_lit 1099511627776) (nat_lit 138968226547)
  (nat_lit 3435973836800000) false (nat_lit 414784401773992769224704) (nat_lit 754488431583)
  (nat_lit 1099511627776) (nat_lit 8757391860671) (nat_lit 3435973836800000)

noncomputable def p130511 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 39))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 38))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 38)) p129095))
  false (nat_lit 449141405517) (nat_lit 549755813888)

noncomputable def p130512 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 38))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 38)) p129095)
  false (nat_lit 210987882757) (nat_lit 274877906944) (nat_lit 2119442883239)

noncomputable def p130513 :=
@p130512 (nat_lit 858993459200000) false (nat_lit 120032718131) (nat_lit 1099511627776)
  (nat_lit 8461968254831) (nat_lit 3435973836800000) false (nat_lit 27165640003) (nat_lit 549755813888)
  (nat_lit 69933347459) (nat_lit 1717986918400000)

noncomputable def p130514 :=
@p130513 true (nat_lit 21235919143) (nat_lit 137438953472) (nat_lit 17748703271)
  (nat_lit 429496729600000) false (nat_lit 123459049470399294210048) (nat_lit 449141405517) (nat_lit 549755813888)
  (nat_lit 4308819113937) (nat_lit 1717986918400000)

noncomputable def p130515 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 38))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 37))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 37)) p129095))
  false (nat_lit 210987882757) (nat_lit 274877906944)

noncomputable def p130516 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 37))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 37)) p129095)
  false (nat_lit 663321873633) (nat_lit 1099511627776) (nat_lit 8333763901357)

noncomputable def p130517 :=
@p130516 (nat_lit 3435973836800000) false (nat_lit 56602360333) (nat_lit 549755813888)
  (nat_lit 4160555652241) (nat_lit 1717986918400000) false (nat_lit 180629657395) (nat_lit 1099511627776)
  (nat_lit 144007631599) (nat_lit 3435973836800000)

noncomputable def p130518 :=
@p130517 false (nat_lit 6827997465) (nat_lit 1099511627776) (nat_lit 140856950349)
  (nat_lit 3435973836800000) false (nat_lit 927934521644643650633728) (nat_lit 210987882757) (nat_lit 274877906944)
  (nat_lit 2119442883239) (nat_lit 858993459200000)

noncomputable def p130519 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 37))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 36))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 36)) p129095))
  false (nat_lit 663321873633) (nat_lit 1099511627776)

noncomputable def p130520 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 36))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 36)) p129095)
  false (nat_lit 78400865615) (nat_lit 137438953472) (nat_lit 4095221791803)

noncomputable def p130521 :=
@p130520 (nat_lit 1717986918400000) true (nat_lit 66453565727) (nat_lit 1099511627776)
  (nat_lit 8175224236731) (nat_lit 3435973836800000) false (nat_lit 36114948713) (nat_lit 1099511627776)
  (nat_lit 143320317751) (nat_lit 3435973836800000)

noncomputable def p130522 :=
@p130521 false (nat_lit 179658286393) (nat_lit 1099511627776) (nat_lit 145887067751)
  (nat_lit 3435973836800000) false (nat_lit 91166264127205750603776) (nat_lit 663321873633) (nat_lit 1099511627776)
  (nat_lit 8333763901357) (nat_lit 3435973836800000)

noncomputable def p130523 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 36))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 35))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 35)) p129095))
  false (nat_lit 78400865615) (nat_lit 137438953472)

noncomputable def p130524 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 35))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 35)) p129095)
  false (nat_lit 798609429139) (nat_lit 1099511627776) (nat_lit 8042723991303)

noncomputable def p130525 :=
@p130524 (nat_lit 3435973836800000) true (nat_lit 69148836677) (nat_lit 549755813888)
  (nat_lit 2007314998607) (nat_lit 858993459200000) true (nat_lit 171402504219) (nat_lit 1099511627776)
  (nat_lit 147719592303) (nat_lit 3435973836800000)

noncomputable def p130526 :=
@p130525 false (nat_lit 71844107627) (nat_lit 1099511627776) (nat_lit 145964242303)
  (nat_lit 3435973836800000) false (nat_lit 689621306971168618577920) (nat_lit 78400865615) (nat_lit 137438953472)
  (nat_lit 4095221791803) (nat_lit 1717986918400000)

noncomputable def p130527 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 35))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 34))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 34)) p129095))
  false (nat_lit 798609429139) (nat_lit 1099511627776)

noncomputable def p130528 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 34))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 34)) p129095)
  false (nat_lit 898080401857) (nat_lit 1099511627776) (nat_lit 7894185087833)

noncomputable def p130529 :=
@p130528 (nat_lit 3435973836800000) false (nat_lit 2736974767) (nat_lit 137438953472)
  (nat_lit 3939832939229) (nat_lit 1717986918400000) true (nat_lit 49735486359) (nat_lit 549755813888)
  (nat_lit 14853890347) (nat_lit 343597383680000)

noncomputable def p130530 :=
@p130529 true (nat_lit 80096735745) (nat_lit 549755813888) (nat_lit 14959411597)
  (nat_lit 343597383680000) false (nat_lit 439040176694942008082432) (nat_lit 798609429139) (nat_lit 1099511627776)
  (nat_lit 8042723991303) (nat_lit 3435973836800000)

noncomputable def p130531 :=
@Enclosure.Complex.IsNear.of_eq (p129093 (nat_lit 34))
  (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
    (p129093 (nat_lit 33))
    (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
      (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 33)) p129095))
  false (nat_lit 898080401857) (nat_lit 1099511627776)

noncomputable def p130532 :=
@Enclosure.Complex.IsNear.addLitP (p129093 (nat_lit 33))
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 33)) p129095)
  false (nat_lit 748337629977) (nat_lit 1099511627776) (nat_lit 7742033207027)

noncomputable def p130533 :=
@p130532 (nat_lit 3435973836800000) false (nat_lit 141105362441) (nat_lit 1099511627776)
  (nat_lit 7728036732027) (nat_lit 3435973836800000) false (nat_lit 18717846485) (nat_lit 137438953472)
  (nat_lit 76075940403) (nat_lit 1717986918400000)

noncomputable def p130534 :=
@p130533 true (nat_lit 119209564305) (nat_lit 1099511627776) (nat_lit 151629146431)
  (nat_lit 3435973836800000) false (nat_lit 123431230564939285397504) (nat_lit 898080401857)
  (nat_lit 1099511627776) (nat_lit 7894185087833) (nat_lit 3435973836800000)

noncomputable def p130535 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 33)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1)))))) }

noncomputable def p130536 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 33)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130537 :=
@p130535 false (nat_lit 18717846485) (nat_lit 137438953472) (nat_lit 76075940403)
  (nat_lit 1717986918400000) true (nat_lit 119209564305) (nat_lit 1099511627776) (nat_lit 151629146431)
  (nat_lit 3435973836800000) p130536

noncomputable def p130538 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1)))))))
  false

noncomputable def p130539 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1)))))
  (nat_lit 182533) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130540 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1)))))
  false (nat_lit 820360) (nat_lit 1048576)

noncomputable def p130541 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 87203)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 512)))
  false (nat_lit 87203) (nat_lit 512)

noncomputable def p130542 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1))))
  false (nat_lit 767045703475251627141) (nat_lit 4503599627370496000) (nat_lit 48711000048711)

noncomputable def p130543 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 15746868335186131) (nat_lit 4503599627370496)

noncomputable def p130544 :=
@p130543 (nat_lit 1000000001) (nat_lit 200000000000000) (nat_lit 767045703475251627141)
  (nat_lit 4503599627370496000) (nat_lit 48711000048711) (nat_lit 200000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 33) (nat_lit 1) (nat_lit 15746868335186131) (nat_lit 4503599627370496)
    (nat_lit 1000000001) (nat_lit 200000000000000) false
    (@p33009 (nat_lit 1000000001000000) (nat_lit 200000000000000000000) (nat_lit 15746868335186131)
      (nat_lit 4503599627370496) (nat_lit 1000000001) (nat_lit 200000000000000)
      (p33014 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130545 :=
BSN.cos_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 87203)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 512)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 49611122221591822336))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 73786976294838206464)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130546 :=
BSN.sin_reduce_arg_pos_rat_q0 (nat_lit 87203) (nat_lit 512) (nat_lit 226375608064910080) (nat_lit 72057594037927936)
  (nat_lit 27) (nat_lit 49611122221591822336) (nat_lit 73786976294838206464) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130547 :=
nat_lit 155309628181946471904792672912592211760258522175715689795466342730769631079361

noncomputable def p130548 :=
nat_lit 18890072305585149946730960811617283758505563741994505384212601671958457281

noncomputable def p130549 :=
nat_lit 465891104401228245414484556816153400713258555399663080375630602988964976323521

noncomputable def p130550 :=
BSN.cos_dyadic_bound_f (nat_lit 1443873689) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130547 p31681 p130548
  p130549 p31684

noncomputable def p130551 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 1443873689)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130547 p31681 p130548 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130552 :=
p130550 p130548 (nat_lit 820360) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130551 (Eq.refl true))

noncomputable def p130553 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 1443873689)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130549 p31684 p130548 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130554 :=
@BSN.cos_arg_round false (nat_lit 820360) (nat_lit 1048576) (nat_lit 49611122221591822336)
  (nat_lit 73786976294838206464) (nat_lit 1443873689) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130552 (p130553 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130555 :=
p130545 (nat_lit 820360) (nat_lit 1048576) (nat_lit 27) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130546 BSN.pi_near_15 p130554 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130556 :=
@p130541 (nat_lit 257) (nat_lit 1048576) false (nat_lit 820360) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130542 (nat_lit 200000000000000000) (nat_lit 87203) (nat_lit 512) (nat_lit 257) (nat_lit 1048576)
    p130544 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 87203) (nat_lit 512))
  (p130555 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130557 :=
@p130539 (nat_lit 1048576) (nat_lit 102545) (nat_lit 131072) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 18717846485) (nat_lit 137438953472) (nat_lit 76075940403) (nat_lit 1717986918400000)
  (@p32999 (nat_lit 182533) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33004
    (Eq.refl true))
  (@p130540 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 102545) (nat_lit 131072)
    (nat_lit 819509) (nat_lit 3276800000) (p130556 (Eq.refl true))
    (Eq.refl true))

noncomputable def p130558 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 33))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1))))))
  (nat_lit 182533) (nat_lit 1048576)

noncomputable def p130559 :=
@p130558 (nat_lit 1) (nat_lit 1048576) (nat_lit 653085) (nat_lit 1048576) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 119209564305) (nat_lit 1099511627776) (nat_lit 151629146431) (nat_lit 3435973836800000)
  (@p32999 (nat_lit 182533) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33004
    (Eq.refl true))

noncomputable def p130560 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1)))))
  false (nat_lit 653085) (nat_lit 1048576)

noncomputable def p130561 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1)))))
  false (nat_lit 653085) (nat_lit 1048576)

noncomputable def p130562 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 33) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 87203)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 512)))
  false (nat_lit 87203) (nat_lit 512)

noncomputable def p130563 :=
BSN.sin_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 87203)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 512)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 49611122221591822336))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 73786976294838206464)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130564 :=
nat_lit 4346271080545385165716989267111375841

noncomputable def p130565 :=
BSN.sin_dyadic_bound_f (nat_lit 1443873689) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130564 p31525 p130564
  p130564 p31526

noncomputable def p130566 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1443873689)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130564 p31525 p130564 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130567 :=
p130565 p130564 (nat_lit 653085) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130566 (Eq.refl true))

noncomputable def p130568 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1443873689)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130564 p31526 p130564 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130569 :=
@BSN.sin_arg_round false (nat_lit 653085) (nat_lit 1048576) (nat_lit 49611122221591822336)
  (nat_lit 73786976294838206464) (nat_lit 1443873689) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130567 (p130568 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130570 :=
p130563 (nat_lit 653085) (nat_lit 1048576) (nat_lit 27) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130546 BSN.pi_near_15 p130569 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130571 :=
@p130562 (nat_lit 257) (nat_lit 1048576) false (nat_lit 653085) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130542 (nat_lit 200000000000000000) (nat_lit 87203) (nat_lit 512) (nat_lit 257) (nat_lit 1048576)
    p130544 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 87203) (nat_lit 512))
  (p130570 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130572 :=
p130559
  (@p130560 (nat_lit 819509) (nat_lit 3276800000)
    (@p130561 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 653085) (nat_lit 1048576)
      (nat_lit 819509) (nat_lit 3276800000) (p130571 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130573 :=
@p130538 (nat_lit 18717846485) (nat_lit 137438953472) (nat_lit 76075940403) (nat_lit 1717986918400000)
  true (nat_lit 119209564305) (nat_lit 1099511627776) (nat_lit 151629146431) (nat_lit 3435973836800000)
  (p130557 (Eq.refl true)) p130572

noncomputable def p130574 :=
@p130534 false (nat_lit 24074684649968066625536) (nat_lit 2736974767) (nat_lit 137438953472)
  (nat_lit 3939832939229) (nat_lit 1717986918400000) d1199
  (p130537 p130573) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130575 :=
p130574 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130576 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 34)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1)))))) }

noncomputable def p130577 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 34)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130578 :=
@p130576 true (nat_lit 49735486359) (nat_lit 549755813888) (nat_lit 14853890347)
  (nat_lit 343597383680000) true (nat_lit 80096735745) (nat_lit 549755813888) (nat_lit 14959411597)
  (nat_lit 343597383680000) p130577

noncomputable def p130579 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1)))))))
  true

noncomputable def p130580 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1)))))
  (nat_lit 179829) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130581 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1)))))
  true (nat_lit 553142) (nat_lit 1048576)

noncomputable def p130582 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11257281)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  false (nat_lit 11257281) (nat_lit 65536)

noncomputable def p130583 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1))))
  false (nat_lit 773594462255761310853) (nat_lit 4503599627370496000) (nat_lit 48711000048711)

noncomputable def p130584 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 15881309401485523) (nat_lit 4503599627370496)

noncomputable def p130585 :=
@p130584 (nat_lit 1000000001) (nat_lit 200000000000000) (nat_lit 773594462255761310853)
  (nat_lit 4503599627370496000) (nat_lit 48711000048711) (nat_lit 200000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 34) (nat_lit 1) (nat_lit 15881309401485523) (nat_lit 4503599627370496)
    (nat_lit 1000000001) (nat_lit 200000000000000) false
    (@p33059 (nat_lit 1000000001000000) (nat_lit 200000000000000000000) (nat_lit 15881309401485523)
      (nat_lit 4503599627370496) (nat_lit 1000000001) (nat_lit 200000000000000)
      (p33064 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130586 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11257281)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5248216872286643290112))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9444732965739290427392)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130587 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 11257281) (nat_lit 65536) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 27) (nat_lit 5248216872286643290112) (nat_lit 9444732965739290427392)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130588 :=
nat_lit 2027719229589522656535988036267808161

noncomputable def p130589 :=
BSN.sin_dyadic_bound_f (nat_lit 1193306359) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130588 p31525 p130588
  p130588 p31526

noncomputable def p130590 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1193306359)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130588 p31525 p130588 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130591 :=
p130589 p130588 (nat_lit 553142) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130590 (Eq.refl true))

noncomputable def p130592 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1193306359)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130588 p31526 p130588 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130593 :=
@BSN.sin_arg_round false (nat_lit 553142) (nat_lit 1048576) (nat_lit 5248216872286643290112)
  (nat_lit 9444732965739290427392) (nat_lit 1193306359) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130591 (p130592 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130594 :=
p130586 (nat_lit 553142) (nat_lit 1048576) (nat_lit 27) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130587 BSN.pi_near_15 p130593 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130595 :=
@p130582 (nat_lit 1) (nat_lit 4096) true (nat_lit 553142) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130583 (nat_lit 200000000000000000) (nat_lit 11257281) (nat_lit 65536) (nat_lit 1) (nat_lit 4096)
    p130585 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 11257281) (nat_lit 65536))
  (p130594 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130596 :=
@p130580 (nat_lit 1048576) (nat_lit 276571) (nat_lit 524288) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 49735486359) (nat_lit 549755813888) (nat_lit 14853890347) (nat_lit 343597383680000)
  (@p33049 (nat_lit 179829) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33054
    (Eq.refl true))
  (@p130581 (nat_lit 204096) (nat_lit 819200000) (nat_lit 276571) (nat_lit 524288) (nat_lit 3189)
    (nat_lit 12800000) (p130595 (Eq.refl true)) (Eq.refl true))

noncomputable def p130597 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 34))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1))))))
  (nat_lit 179829) (nat_lit 1048576)

noncomputable def p130598 :=
@p130597 (nat_lit 1) (nat_lit 1048576) (nat_lit 445405) (nat_lit 524288) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 80096735745) (nat_lit 549755813888) (nat_lit 14959411597) (nat_lit 343597383680000)
  (@p33049 (nat_lit 179829) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33054
    (Eq.refl true))

noncomputable def p130599 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1)))))
  false (nat_lit 445405) (nat_lit 524288)

noncomputable def p130600 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1)))))
  false (nat_lit 890810) (nat_lit 1048576)

noncomputable def p130601 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 34) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11257281)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  false (nat_lit 11257281) (nat_lit 65536)

noncomputable def p130602 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 11257281)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 65536)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 5248216872286643290112))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 9444732965739290427392)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130603 :=
BSN.cos_dyadic_bound_f (nat_lit 1193306359) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130588 p31541 p130588
  p130588 p31542

noncomputable def p130604 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 1193306359)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130588 p31541 p130588 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130605 :=
p130603 p130588 (nat_lit 890810) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130604 (Eq.refl true))

noncomputable def p130606 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 1193306359)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130588 p31542 p130588 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130607 :=
@BSN.cos_arg_round false (nat_lit 890810) (nat_lit 1048576) (nat_lit 5248216872286643290112)
  (nat_lit 9444732965739290427392) (nat_lit 1193306359) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130605 (p130606 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130608 :=
p130602 (nat_lit 890810) (nat_lit 1048576) (nat_lit 27) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130587 BSN.pi_near_15 p130607 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130609 :=
@p130601 (nat_lit 1) (nat_lit 4096) false (nat_lit 890810) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130583 (nat_lit 200000000000000000) (nat_lit 11257281) (nat_lit 65536) (nat_lit 1) (nat_lit 4096)
    p130585 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 11257281) (nat_lit 65536))
  (p130608 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130610 :=
p130598
  (@p130599 (nat_lit 3189) (nat_lit 12800000)
    (@p130600 (nat_lit 204096) (nat_lit 819200000) (nat_lit 445405) (nat_lit 524288) (nat_lit 3189)
      (nat_lit 12800000) (p130609 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130611 :=
@p130579 (nat_lit 49735486359) (nat_lit 549755813888) (nat_lit 14853890347) (nat_lit 343597383680000)
  true (nat_lit 80096735745) (nat_lit 549755813888) (nat_lit 14959411597) (nat_lit 343597383680000)
  (p130596 (Eq.refl true)) p130610

noncomputable def p130612 :=
@p130530 true (nat_lit 9503743746693130092544) (nat_lit 69148836677) (nat_lit 549755813888)
  (nat_lit 2007314998607) (nat_lit 858993459200000)
  (@p130531 (nat_lit 7894185087833) (nat_lit 3435973836800000) false (nat_lit 2736974767)
    (nat_lit 137438953472) (nat_lit 3939832939229) (nat_lit 1717986918400000)
    (p129097 (nat_lit 33) (nat_lit 34) (Eq.refl true) (Eq.refl true))
    (p130575 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (p130578 p130611)

noncomputable def p130613 :=
p130612 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130614 :=
p130613 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130615 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 35)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1)))))) }

noncomputable def p130616 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 35)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130617 :=
@p130615 true (nat_lit 171402504219) (nat_lit 1099511627776) (nat_lit 147719592303)
  (nat_lit 3435973836800000) false (nat_lit 71844107627) (nat_lit 1099511627776) (nat_lit 145964242303)
  (nat_lit 3435973836800000) p130616

noncomputable def p130618 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1)))))))
  true

noncomputable def p130619 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1)))))
  (nat_lit 177241) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130620 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1)))))
  true (nat_lit 967059) (nat_lit 1048576)

noncomputable def p130621 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 45399279)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  false (nat_lit 45399279) (nat_lit 262144)

noncomputable def p130622 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1))))
  false (nat_lit 779953674826599351429) (nat_lit 4503599627370496000) (nat_lit 48711000048711)

noncomputable def p130623 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 16011859227414739) (nat_lit 4503599627370496)

noncomputable def p130624 :=
@p130623 (nat_lit 1000000001) (nat_lit 200000000000000) (nat_lit 779953674826599351429)
  (nat_lit 4503599627370496000) (nat_lit 48711000048711) (nat_lit 200000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 35) (nat_lit 1) (nat_lit 16011859227414739) (nat_lit 4503599627370496)
    (nat_lit 1000000001) (nat_lit 200000000000000) false
    (@p33110 (nat_lit 1000000001000000) (nat_lit 200000000000000000000) (nat_lit 16011859227414739)
      (nat_lit 4503599627370496) (nat_lit 1000000001) (nat_lit 200000000000000)
      (p33115 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130625 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 45399279)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14994817530797215449088))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37778931862957161709568)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130626 :=
BSN.sin_reduce_arg_pos_rat_q2 (nat_lit 45399279) (nat_lit 262144) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 27) (nat_lit 14994817530797215449088) (nat_lit 37778931862957161709568)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130627 :=
nat_lit 527819587486430305459468981560270001

noncomputable def p130628 :=
BSN.cos_dyadic_bound_f (nat_lit 852356693) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130627 p31541 p130627
  p130627 p31542

noncomputable def p130629 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 852356693)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130627 p31541 p130627 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130630 :=
p130628 p130627 (nat_lit 967059) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130629 (Eq.refl true))

noncomputable def p130631 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 852356693)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130627 p31542 p130627 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130632 :=
@BSN.cos_arg_round false (nat_lit 967059) (nat_lit 1048576) (nat_lit 14994817530797215449088)
  (nat_lit 37778931862957161709568) (nat_lit 852356693) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130630 (p130631 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130633 :=
p130625 (nat_lit 967059) (nat_lit 1048576) (nat_lit 27) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130626 BSN.pi_near_15 p130632 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130634 :=
@p130621 (nat_lit 1) (nat_lit 4096) true (nat_lit 967059) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130622 (nat_lit 200000000000000000) (nat_lit 45399279) (nat_lit 262144) (nat_lit 1)
    (nat_lit 4096) p130624 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 45399279) (nat_lit 262144))
  (p130633 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130635 :=
@p130619 (nat_lit 1048576) (nat_lit 967059) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 171402504219) (nat_lit 1099511627776) (nat_lit 147719592303) (nat_lit 3435973836800000)
  (@p33100 (nat_lit 177241) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33105
    (Eq.refl true))
  (@p130620 (nat_lit 204096) (nat_lit 819200000) (nat_lit 967059) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p130634 (Eq.refl true)) (Eq.refl true))

noncomputable def p130636 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 35))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1))))))
  (nat_lit 177241) (nat_lit 1048576)

noncomputable def p130637 :=
@p130636 (nat_lit 1) (nat_lit 1048576) (nat_lit 405347) (nat_lit 1048576) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 71844107627) (nat_lit 1099511627776) (nat_lit 145964242303) (nat_lit 3435973836800000)
  (@p33100 (nat_lit 177241) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33105
    (Eq.refl true))

noncomputable def p130638 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1)))))
  true (nat_lit 405347) (nat_lit 1048576)

noncomputable def p130639 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1)))))
  true (nat_lit 405347) (nat_lit 1048576)

noncomputable def p130640 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 35) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 45399279)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  false (nat_lit 45399279) (nat_lit 262144)

noncomputable def p130641 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 45399279)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 14994817530797215449088))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37778931862957161709568)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130642 :=
BSN.sin_dyadic_bound_f (nat_lit 852356693) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130627 p31525 p130627
  p130627 p31526

noncomputable def p130643 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 852356693)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130627 p31525 p130627 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130644 :=
p130642 p130627 (nat_lit 405347) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130643 (Eq.refl true))

noncomputable def p130645 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 852356693)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130627 p31526 p130627 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130646 :=
@BSN.sin_arg_round false (nat_lit 405347) (nat_lit 1048576) (nat_lit 14994817530797215449088)
  (nat_lit 37778931862957161709568) (nat_lit 852356693) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130644 (p130645 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130647 :=
p130641 (nat_lit 405347) (nat_lit 1048576) (nat_lit 27) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130626 BSN.pi_near_15 p130646 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130648 :=
@p130640 (nat_lit 1) (nat_lit 4096) true (nat_lit 405347) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130622 (nat_lit 200000000000000000) (nat_lit 45399279) (nat_lit 262144) (nat_lit 1)
    (nat_lit 4096) p130624 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 45399279) (nat_lit 262144))
  (p130647 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130649 :=
p130637
  (@p130638 (nat_lit 3189) (nat_lit 12800000)
    (@p130639 (nat_lit 204096) (nat_lit 819200000) (nat_lit 405347) (nat_lit 1048576) (nat_lit 3189)
      (nat_lit 12800000) (p130648 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130650 :=
@p130618 (nat_lit 171402504219) (nat_lit 1099511627776) (nat_lit 147719592303)
  (nat_lit 3435973836800000) false (nat_lit 71844107627) (nat_lit 1099511627776) (nat_lit 145964242303)
  (nat_lit 3435973836800000) (p130635 (Eq.refl true)) p130649

noncomputable def p130651 :=
@p130526 true (nat_lit 36533234112006587416576) (nat_lit 66453565727) (nat_lit 1099511627776)
  (nat_lit 8175224236731) (nat_lit 3435973836800000)
  (@p130527 (nat_lit 8042723991303) (nat_lit 3435973836800000) true (nat_lit 69148836677)
    (nat_lit 549755813888) (nat_lit 2007314998607) (nat_lit 858993459200000)
    (p129097 (nat_lit 34) (nat_lit 35) (Eq.refl true) (Eq.refl true))
    p130614)
  (p130617 p130650)

noncomputable def p130652 :=
p130651 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130653 :=
p130652 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130654 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 36)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1)))))) }

noncomputable def p130655 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 36)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130656 :=
@p130654 false (nat_lit 36114948713) (nat_lit 1099511627776) (nat_lit 143320317751)
  (nat_lit 3435973836800000) false (nat_lit 179658286393) (nat_lit 1099511627776) (nat_lit 145887067751)
  (nat_lit 3435973836800000) p130655

noncomputable def p130657 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1)))))))
  false

noncomputable def p130658 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1)))))
  (nat_lit 174763) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130659 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1)))))
  false (nat_lit 206651) (nat_lit 1048576)

noncomputable def p130660 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 183036039)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 183036039) (nat_lit 1048576)

noncomputable def p130661 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1))))
  false (nat_lit 786133801795363521669) (nat_lit 4503599627370496000) (nat_lit 48711000048711)

noncomputable def p130662 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 16138732561338579) (nat_lit 4503599627370496)

noncomputable def p130663 :=
@p130662 (nat_lit 1000000001) (nat_lit 200000000000000) (nat_lit 786133801795363521669)
  (nat_lit 4503599627370496000) (nat_lit 48711000048711) (nat_lit 200000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 36) (nat_lit 1) (nat_lit 16138732561338579) (nat_lit 4503599627370496)
    (nat_lit 1000000001) (nat_lit 200000000000000) false
    (@p33161 (nat_lit 1000000001000000) (nat_lit 200000000000000000000) (nat_lit 16138732561338579)
      (nat_lit 4503599627370496) (nat_lit 1000000001) (nat_lit 200000000000000)
      (p33166 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130664 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 183036039)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29977899292592468656128))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130665 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 183036039) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 27) (nat_lit 29977899292592468656128) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130666 :=
nat_lit 32937116881175820657384195866817681

noncomputable def p130667 :=
BSN.sin_dyadic_bound_f (nat_lit 426011571) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130666 p31525 p130666
  p130666 p31526

noncomputable def p130668 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 426011571)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130666 p31525 p130666 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130669 :=
p130667 p130666 (nat_lit 206651) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130668 (Eq.refl true))

noncomputable def p130670 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 426011571)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130666 p31526 p130666 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130671 :=
@BSN.sin_arg_round false (nat_lit 206651) (nat_lit 1048576) (nat_lit 29977899292592468656128)
  (nat_lit 151115727451828646838272) (nat_lit 426011571) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130669 (p130670 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130672 :=
p130664 (nat_lit 206651) (nat_lit 1048576) (nat_lit 27) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130665 BSN.pi_near_15 p130671 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130673 :=
@p130660 (nat_lit 1) (nat_lit 4096) false (nat_lit 206651) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130661 (nat_lit 200000000000000000) (nat_lit 183036039) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130663 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 183036039) (nat_lit 1048576))
  (p130672 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130674 :=
@p130658 (nat_lit 1048576) (nat_lit 206651) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 36114948713) (nat_lit 1099511627776) (nat_lit 143320317751) (nat_lit 3435973836800000)
  (@p33151 (nat_lit 174763) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33156
    (Eq.refl true))
  (@p130659 (nat_lit 204096) (nat_lit 819200000) (nat_lit 206651) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p130673 (Eq.refl true)) (Eq.refl true))

noncomputable def p130675 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 36))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1))))))
  (nat_lit 174763) (nat_lit 1048576)

noncomputable def p130676 :=
@p130675 (nat_lit 1) (nat_lit 1048576) (nat_lit 1028011) (nat_lit 1048576) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 179658286393) (nat_lit 1099511627776) (nat_lit 145887067751) (nat_lit 3435973836800000)
  (@p33151 (nat_lit 174763) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33156
    (Eq.refl true))

noncomputable def p130677 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1)))))
  true (nat_lit 1028011) (nat_lit 1048576)

noncomputable def p130678 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1)))))
  true (nat_lit 1028011) (nat_lit 1048576)

noncomputable def p130679 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 36) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 183036039)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 183036039) (nat_lit 1048576)

noncomputable def p130680 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 183036039)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 29977899292592468656128))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130681 :=
BSN.cos_dyadic_bound_f (nat_lit 426011571) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130666 p31541 p130666
  p130666 p31542

noncomputable def p130682 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 426011571)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130666 p31541 p130666 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130683 :=
p130681 p130666 (nat_lit 1028011) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130682 (Eq.refl true))

noncomputable def p130684 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 426011571)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130666 p31542 p130666 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130685 :=
@BSN.cos_arg_round false (nat_lit 1028011) (nat_lit 1048576) (nat_lit 29977899292592468656128)
  (nat_lit 151115727451828646838272) (nat_lit 426011571) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130683 (p130684 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130686 :=
p130680 (nat_lit 1028011) (nat_lit 1048576) (nat_lit 27) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130665 BSN.pi_near_15 p130685 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130687 :=
@p130679 (nat_lit 1) (nat_lit 4096) true (nat_lit 1028011) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130661 (nat_lit 200000000000000000) (nat_lit 183036039) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130663 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 183036039) (nat_lit 1048576))
  (p130686 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130688 :=
p130676
  (@p130677 (nat_lit 3189) (nat_lit 12800000)
    (@p130678 (nat_lit 204096) (nat_lit 819200000) (nat_lit 1028011) (nat_lit 1048576) (nat_lit 3189)
      (nat_lit 12800000) (p130687 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130689 :=
@p130657 (nat_lit 36114948713) (nat_lit 1099511627776) (nat_lit 143320317751)
  (nat_lit 3435973836800000) false (nat_lit 179658286393) (nat_lit 1099511627776) (nat_lit 145887067751)
  (nat_lit 3435973836800000) (p130674 (Eq.refl true)) p130688

noncomputable def p130690 :=
@p130522 false (nat_lit 124469906691401046818816) (nat_lit 56602360333) (nat_lit 549755813888)
  (nat_lit 4160555652241) (nat_lit 1717986918400000)
  (@p130523 (nat_lit 4095221791803) (nat_lit 1717986918400000) true (nat_lit 66453565727)
    (nat_lit 1099511627776) (nat_lit 8175224236731) (nat_lit 3435973836800000)
    (p129097 (nat_lit 35) (nat_lit 36) (Eq.refl true) (Eq.refl true))
    p130653)
  (p130656 p130689)

noncomputable def p130691 :=
p130690 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130692 :=
p130691 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130693 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 37)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1)))))) }

noncomputable def p130694 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 37)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130695 :=
@p130693 false (nat_lit 180629657395) (nat_lit 1099511627776) (nat_lit 144007631599)
  (nat_lit 3435973836800000) false (nat_lit 6827997465) (nat_lit 1099511627776) (nat_lit 140856950349)
  (nat_lit 3435973836800000) p130694

noncomputable def p130696 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1)))))))
  false

noncomputable def p130697 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1)))))
  (nat_lit 172385) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130698 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1)))))
  false (nat_lit 1047827) (nat_lit 1048576)

noncomputable def p130699 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 92217753)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 92217753) (nat_lit 524288)

noncomputable def p130700 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1))))
  false (nat_lit 792144466921043772549) (nat_lit 4503599627370496000) (nat_lit 48711000048711)

noncomputable def p130701 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 16262126971752659) (nat_lit 4503599627370496)

noncomputable def p130702 :=
@p130701 (nat_lit 1000000001) (nat_lit 200000000000000) (nat_lit 792144466921043772549)
  (nat_lit 4503599627370496000) (nat_lit 48711000048711) (nat_lit 200000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 37) (nat_lit 1) (nat_lit 16262126971752659) (nat_lit 4503599627370496)
    (nat_lit 1000000001) (nat_lit 200000000000000) false
    (@p33212 (nat_lit 1000000001000000) (nat_lit 200000000000000000000) (nat_lit 16262126971752659)
      (nat_lit 4503599627370496) (nat_lit 1000000001) (nat_lit 200000000000000)
      (p33217 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130703 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 92217753)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 115831174601773129138176))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130704 :=
BSN.sin_reduce_arg_pos_rat_q3 (nat_lit 92217753) (nat_lit 524288) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 27) (nat_lit 115831174601773129138176) (nat_lit 75557863725914323419136)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130705 :=
nat_lit 7568265393207442512049685830026738474728560520532616890443893253976886341990945

noncomputable def p130706 :=
nat_lit 13797653792460649531971970542823123167340385710673070005704940600367327410721

noncomputable def p130707 :=
nat_lit 19799308399879317908506936840619744282018155024530049742581912428015059984644641

noncomputable def p130708 :=
BSN.sin_dyadic_bound_f (nat_lit 3292119987) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130705 p31776 p130706
  p130707 p31779

noncomputable def p130709 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 3292119987)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130705 p31776 p130706 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130710 :=
p130708 p130706 (nat_lit 1047827) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130709 (Eq.refl true))

noncomputable def p130711 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 3292119987)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130707 p31779 p130706 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130712 :=
@BSN.sin_arg_round false (nat_lit 1047827) (nat_lit 1048576) (nat_lit 115831174601773129138176)
  (nat_lit 75557863725914323419136) (nat_lit 3292119987) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130710 (p130711 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130713 :=
p130703 (nat_lit 1047827) (nat_lit 1048576) (nat_lit 27) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130704 BSN.pi_near_15 p130712 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130714 :=
@p130699 (nat_lit 1) (nat_lit 4096) false (nat_lit 1047827) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130700 (nat_lit 200000000000000000) (nat_lit 92217753) (nat_lit 524288) (nat_lit 1)
    (nat_lit 4096) p130702 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 92217753) (nat_lit 524288))
  (p130713 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130715 :=
@p130697 (nat_lit 1048576) (nat_lit 1047827) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 180629657395) (nat_lit 1099511627776) (nat_lit 144007631599) (nat_lit 3435973836800000)
  (@p33202 (nat_lit 172385) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33207
    (Eq.refl true))
  (@p130698 (nat_lit 204096) (nat_lit 819200000) (nat_lit 1047827) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p130714 (Eq.refl true)) (Eq.refl true))

noncomputable def p130716 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1))))))
  (nat_lit 172385) (nat_lit 1048576)

noncomputable def p130717 :=
@p130716 (nat_lit 1) (nat_lit 1048576) (nat_lit 39609) (nat_lit 1048576) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 6827997465) (nat_lit 1099511627776) (nat_lit 140856950349) (nat_lit 3435973836800000)
  (@p33202 (nat_lit 172385) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33207
    (Eq.refl true))

noncomputable def p130718 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1)))))
  true (nat_lit 39609) (nat_lit 1048576)

noncomputable def p130719 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1)))))
  true (nat_lit 39609) (nat_lit 1048576)

noncomputable def p130720 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 37) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 92217753)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  false (nat_lit 92217753) (nat_lit 524288)

noncomputable def p130721 :=
BSN.sin_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 92217753)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 524288)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 115831174601773129138176))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 75557863725914323419136)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130722 :=
nat_lit 4210724175689672795375146336922776096256907127278419636915809559142877891066401

noncomputable def p130723 :=
nat_lit 12604577219484097087061495069682682042436040610413912770736018796227899018377761

noncomputable def p130724 :=
BSN.cos_dyadic_bound_f (nat_lit 3292119987) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130722 p31681 p130706
  p130723 p31684

noncomputable def p130725 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 3292119987)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130722 p31681 p130706 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130726 :=
p130724 p130706 (nat_lit 39609) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130725 (Eq.refl true))

noncomputable def p130727 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 3292119987)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130723 p31684 p130706 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130728 :=
@BSN.cos_arg_round false (nat_lit 39609) (nat_lit 1048576) (nat_lit 115831174601773129138176)
  (nat_lit 75557863725914323419136) (nat_lit 3292119987) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130726 (p130727 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130729 :=
p130721 (nat_lit 39609) (nat_lit 1048576) (nat_lit 27) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130704 BSN.pi_near_15 p130728 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130730 :=
@p130720 (nat_lit 1) (nat_lit 4096) true (nat_lit 39609) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130700 (nat_lit 200000000000000000) (nat_lit 92217753) (nat_lit 524288) (nat_lit 1)
    (nat_lit 4096) p130702 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 92217753) (nat_lit 524288))
  (p130729 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130731 :=
p130717
  (@p130718 (nat_lit 3189) (nat_lit 12800000)
    (@p130719 (nat_lit 204096) (nat_lit 819200000) (nat_lit 39609) (nat_lit 1048576) (nat_lit 3189)
      (nat_lit 12800000) (p130730 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130732 :=
@p130696 (nat_lit 180629657395) (nat_lit 1099511627776) (nat_lit 144007631599)
  (nat_lit 3435973836800000) false (nat_lit 6827997465) (nat_lit 1099511627776) (nat_lit 140856950349)
  (nat_lit 3435973836800000) (p130715 (Eq.refl true)) p130731

noncomputable def p130733 :=
@p130518 false (nat_lit 65988684649296799203328) (nat_lit 120032718131) (nat_lit 1099511627776)
  (nat_lit 8461968254831) (nat_lit 3435973836800000)
  (@p130519 (nat_lit 8333763901357) (nat_lit 3435973836800000) false (nat_lit 56602360333)
    (nat_lit 549755813888) (nat_lit 4160555652241) (nat_lit 1717986918400000)
    (p129097 (nat_lit 36) (nat_lit 37) (Eq.refl true) (Eq.refl true))
    p130692)
  (p130695 p130732)

noncomputable def p130734 :=
p130733 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130735 :=
p130734 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130736 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 38)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1)))))) }

noncomputable def p130737 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 38)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130738 :=
@p130736 false (nat_lit 27165640003) (nat_lit 549755813888) (nat_lit 69933347459)
  (nat_lit 1717986918400000) true (nat_lit 21235919143) (nat_lit 137438953472) (nat_lit 17748703271)
  (nat_lit 429496729600000) p130737

noncomputable def p130739 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1)))))))
  false

noncomputable def p130740 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1)))))
  (nat_lit 170101) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130741 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1)))))
  false (nat_lit 319406) (nat_lit 1048576)

noncomputable def p130742 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 46449415)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  false (nat_lit 46449415) (nat_lit 262144)

noncomputable def p130743 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1))))
  false (nat_lit 797994875538326144133) (nat_lit 4503599627370496000) (nat_lit 48711000048711)

noncomputable def p130744 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 16382231437218003) (nat_lit 4503599627370496)

noncomputable def p130745 :=
@p130744 (nat_lit 1000000001) (nat_lit 200000000000000) (nat_lit 797994875538326144133)
  (nat_lit 4503599627370496000) (nat_lit 48711000048711) (nat_lit 200000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 38) (nat_lit 1) (nat_lit 16382231437218003) (nat_lit 4503599627370496)
    (nat_lit 1000000001) (nat_lit 200000000000000) false
    (@p33263 (nat_lit 1000000001000000) (nat_lit 200000000000000000000) (nat_lit 16382231437218003)
      (nat_lit 4503599627370496) (nat_lit 1000000001) (nat_lit 200000000000000)
      (p33268 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130746 :=
BSN.cos_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 46449415)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 47649349874888621424640))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37778931862957161709568)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130747 :=
BSN.sin_reduce_arg_pos_rat_q0 (nat_lit 46449415) (nat_lit 262144) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 28) (nat_lit 47649349874888621424640) (nat_lit 37778931862957161709568)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130748 :=
nat_lit 1925888426709856940155299213932676350017786641769390206991201754192306939815041

noncomputable def p130749 :=
nat_lit 2896658931388075267265549045273478225106645945036159333914660423062138053761

noncomputable def p130750 :=
nat_lit 5771871962266794669931366543707482093603146633418098302305775941730796543337601

noncomputable def p130751 :=
BSN.cos_dyadic_bound_f (nat_lit 2708551953) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130748 p31681 p130749
  p130750 p31684

noncomputable def p130752 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 2708551953)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130748 p31681 p130749 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130753 :=
p130751 p130749 (nat_lit 319406) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130752 (Eq.refl true))

noncomputable def p130754 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 2708551953)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130750 p31684 p130749 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130755 :=
@BSN.cos_arg_round false (nat_lit 319406) (nat_lit 1048576) (nat_lit 47649349874888621424640)
  (nat_lit 37778931862957161709568) (nat_lit 2708551953) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130753 (p130754 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130756 :=
p130746 (nat_lit 319406) (nat_lit 1048576) (nat_lit 28) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130747 BSN.pi_near_15 p130755 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130757 :=
@p130742 (nat_lit 1) (nat_lit 4096) false (nat_lit 319406) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130743 (nat_lit 200000000000000000) (nat_lit 46449415) (nat_lit 262144) (nat_lit 1)
    (nat_lit 4096) p130745 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 46449415) (nat_lit 262144))
  (p130756 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130758 :=
@p130740 (nat_lit 1048576) (nat_lit 159703) (nat_lit 524288) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 27165640003) (nat_lit 549755813888) (nat_lit 69933347459) (nat_lit 1717986918400000)
  (@p33253 (nat_lit 170101) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33258
    (Eq.refl true))
  (@p130741 (nat_lit 204096) (nat_lit 819200000) (nat_lit 159703) (nat_lit 524288) (nat_lit 3189)
    (nat_lit 12800000) (p130757 (Eq.refl true)) (Eq.refl true))

noncomputable def p130759 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 38))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1))))))
  (nat_lit 170101) (nat_lit 1048576)

noncomputable def p130760 :=
@p130759 (nat_lit 1) (nat_lit 1048576) (nat_lit 124843) (nat_lit 131072) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 21235919143) (nat_lit 137438953472) (nat_lit 17748703271) (nat_lit 429496729600000)
  (@p33253 (nat_lit 170101) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33258
    (Eq.refl true))

noncomputable def p130761 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1)))))
  false (nat_lit 124843) (nat_lit 131072)

noncomputable def p130762 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1)))))
  false (nat_lit 998744) (nat_lit 1048576)

noncomputable def p130763 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 38) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 46449415)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  false (nat_lit 46449415) (nat_lit 262144)

noncomputable def p130764 :=
BSN.sin_reduce0
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 46449415)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 47649349874888621424640))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37778931862957161709568)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130765 :=
nat_lit 3464281840932632032065726145842598647451930638428873445117031429207702781224065

noncomputable def p130766 :=
nat_lit 9068429278458455581167995683514458445247740911974133812575410959620930489214081

noncomputable def p130767 :=
BSN.sin_dyadic_bound_f (nat_lit 2708551953) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130765 p31776 p130749
  p130766 p31779

noncomputable def p130768 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 2708551953)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130765 p31776 p130749 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130769 :=
p130767 p130749 (nat_lit 998744) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130768 (Eq.refl true))

noncomputable def p130770 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 2708551953)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130766 p31779 p130749 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130771 :=
@BSN.sin_arg_round false (nat_lit 998744) (nat_lit 1048576) (nat_lit 47649349874888621424640)
  (nat_lit 37778931862957161709568) (nat_lit 2708551953) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130769 (p130770 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130772 :=
p130764 (nat_lit 998744) (nat_lit 1048576) (nat_lit 28) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130747 BSN.pi_near_15 p130771 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130773 :=
@p130763 (nat_lit 1) (nat_lit 4096) false (nat_lit 998744) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130743 (nat_lit 200000000000000000) (nat_lit 46449415) (nat_lit 262144) (nat_lit 1)
    (nat_lit 4096) p130745 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 46449415) (nat_lit 262144))
  (p130772 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130774 :=
p130760
  (@p130761 (nat_lit 3189) (nat_lit 12800000)
    (@p130762 (nat_lit 204096) (nat_lit 819200000) (nat_lit 124843) (nat_lit 131072) (nat_lit 3189)
      (nat_lit 12800000) (p130773 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130775 :=
@p130739 (nat_lit 27165640003) (nat_lit 549755813888) (nat_lit 69933347459) (nat_lit 1717986918400000)
  true (nat_lit 21235919143) (nat_lit 137438953472) (nat_lit 17748703271) (nat_lit 429496729600000)
  (p130758 (Eq.refl true)) p130774

noncomputable def p130776 :=
@p130514 true (nat_lit 6851968861915249115136) (nat_lit 49854635013) (nat_lit 1099511627776)
  (nat_lit 8603957880999) (nat_lit 3435973836800000)
  (@p130515 (nat_lit 2119442883239) (nat_lit 858993459200000) false (nat_lit 120032718131)
    (nat_lit 1099511627776) (nat_lit 8461968254831) (nat_lit 3435973836800000)
    (p129097 (nat_lit 37) (nat_lit 38) (Eq.refl true) (Eq.refl true))
    p130735)
  (p130738 p130775)

noncomputable def p130777 :=
p130776 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130778 :=
p130777 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130779 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 39)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1)))))) }

noncomputable def p130780 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 39)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130781 :=
@p130779 true (nat_lit 143794379451) (nat_lit 1099511627776) (nat_lit 139753632797)
  (nat_lit 3435973836800000) true (nat_lit 101594313141) (nat_lit 1099511627776) (nat_lit 138968226547)
  (nat_lit 3435973836800000) p130780

noncomputable def p130782 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1)))))))
  true

noncomputable def p130783 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1)))))
  (nat_lit 167907) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130784 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1)))))
  true (nat_lit 856393) (nat_lit 1048576)

noncomputable def p130785 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 187124353)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 187124353) (nat_lit 1048576)

noncomputable def p130786 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1))))
  false (nat_lit 803692977708984943749) (nat_lit 4503599627370496000) (nat_lit 48711000048711)

noncomputable def p130787 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 16499209166491859) (nat_lit 4503599627370496)

noncomputable def p130788 :=
@p130787 (nat_lit 1000000001) (nat_lit 200000000000000) (nat_lit 803692977708984943749)
  (nat_lit 4503599627370496000) (nat_lit 48711000048711) (nat_lit 200000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 39) (nat_lit 1) (nat_lit 16499209166491859) (nat_lit 4503599627370496)
    (nat_lit 1000000001) (nat_lit 200000000000000) false
    (@p33314 (nat_lit 1000000001000000) (nat_lit 200000000000000000000) (nat_lit 16499209166491859)
      (nat_lit 4503599627370496) (nat_lit 1000000001) (nat_lit 200000000000000)
      (p33319 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130789 :=
BSN.cos_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 187124353)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 144421981111204788043776))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130790 :=
BSN.sin_reduce_arg_pos_rat_q1 (nat_lit 187124353) (nat_lit 1048576) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 28) (nat_lit 144421981111204788043776) (nat_lit 151115727451828646838272)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130791 :=
nat_lit 1141392551020059936308587367527219457910080301431985399336581918497111942998145

noncomputable def p130792 :=
nat_lit 314795112114588798785656942393404741047315228838292563367541509526294997121

noncomputable def p130793 :=
nat_lit 2988851774871019070372075851331223543993276564808509286493214719334155373095041

noncomputable def p130794 :=
BSN.sin_dyadic_bound_f (nat_lit 2052359791) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130791 p31776 p130792
  p130793 p31779

noncomputable def p130795 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP (nat_lit 2052359791)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130791 p31776 p130792 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130796 :=
p130794 p130792 (nat_lit 856393) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130795 (Eq.refl true))

noncomputable def p130797 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP (nat_lit 2052359791)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130793 p31779 p130792 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130798 :=
@BSN.sin_arg_round false (nat_lit 856393) (nat_lit 1048576) (nat_lit 144421981111204788043776)
  (nat_lit 151115727451828646838272) (nat_lit 2052359791) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130796 (p130797 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130799 :=
p130789 (nat_lit 856393) (nat_lit 1048576) (nat_lit 28) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130790 BSN.pi_near_15 p130798 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130800 :=
@p130785 (nat_lit 1) (nat_lit 4096) true (nat_lit 856393) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130786 (nat_lit 200000000000000000) (nat_lit 187124353) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130788 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 187124353) (nat_lit 1048576))
  (p130799 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130801 :=
@p130783 (nat_lit 1048576) (nat_lit 856393) (nat_lit 1048576) (nat_lit 3189) (nat_lit 12800000)
  (nat_lit 143794379451) (nat_lit 1099511627776) (nat_lit 139753632797) (nat_lit 3435973836800000)
  (@p33304 (nat_lit 167907) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33309
    (Eq.refl true))
  (@p130784 (nat_lit 204096) (nat_lit 819200000) (nat_lit 856393) (nat_lit 1048576) (nat_lit 3189)
    (nat_lit 12800000) (p130800 (Eq.refl true)) (Eq.refl true))

noncomputable def p130802 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 39))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1))))))
  (nat_lit 167907) (nat_lit 1048576)

noncomputable def p130803 :=
@p130802 (nat_lit 1) (nat_lit 1048576) (nat_lit 605063) (nat_lit 1048576) (nat_lit 3189)
  (nat_lit 12800000) (nat_lit 101594313141) (nat_lit 1099511627776) (nat_lit 138968226547) (nat_lit 3435973836800000)
  (@p33304 (nat_lit 167907) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33309
    (Eq.refl true))

noncomputable def p130804 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1)))))
  false (nat_lit 605063) (nat_lit 1048576)

noncomputable def p130805 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1)))))
  false (nat_lit 605063) (nat_lit 1048576)

noncomputable def p130806 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 39) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 187124353)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  false (nat_lit 187124353) (nat_lit 1048576)

noncomputable def p130807 :=
BSN.sin_reduce1
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 187124353)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 1048576)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 144421981111204788043776))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 151115727451828646838272)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130808 :=
nat_lit 634246881727639781859786607267296767612732307563920018548486639835962766108801

noncomputable def p130809 :=
nat_lit 1902111054958690167981788507917103493356102292234083470518724836488835708332161

noncomputable def p130810 :=
BSN.cos_dyadic_bound_f (nat_lit 2052359791) (nat_lit 2147483648) (nat_lit 3) (nat_lit 2) (nat_lit 1048576)
  (nat_lit 400391) p130808 p31681 p130792
  p130809 p31684

noncomputable def p130811 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP (nat_lit 2052359791)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0)
  (nat_lit 2) p130808 p31681 p130792 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130812 :=
p130810 p130792 (nat_lit 605063) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130811 (Eq.refl true))

noncomputable def p130813 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP (nat_lit 2052359791)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 2)
  p130809 p31684 p130792 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130814 :=
@BSN.cos_arg_round false (nat_lit 605063) (nat_lit 1048576) (nat_lit 144421981111204788043776)
  (nat_lit 151115727451828646838272) (nat_lit 2052359791) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130812 (p130813 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130815 :=
p130807 (nat_lit 605063) (nat_lit 1048576) (nat_lit 28) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130790 BSN.pi_near_15 p130814 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130816 :=
@p130806 (nat_lit 1) (nat_lit 4096) false (nat_lit 605063) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130786 (nat_lit 200000000000000000) (nat_lit 187124353) (nat_lit 1048576) (nat_lit 1)
    (nat_lit 4096) p130788 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 187124353) (nat_lit 1048576))
  (p130815 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130817 :=
p130803
  (@p130804 (nat_lit 3189) (nat_lit 12800000)
    (@p130805 (nat_lit 204096) (nat_lit 819200000) (nat_lit 605063) (nat_lit 1048576) (nat_lit 3189)
      (nat_lit 12800000) (p130816 (Eq.refl true)) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130818 :=
@p130782 (nat_lit 143794379451) (nat_lit 1099511627776) (nat_lit 139753632797)
  (nat_lit 3435973836800000) true (nat_lit 101594313141) (nat_lit 1099511627776) (nat_lit 138968226547)
  (nat_lit 3435973836800000) (p130801 (Eq.refl true)) p130817

noncomputable def p130819 :=
@p130510 true (nat_lit 166519879509767570325504) (nat_lit 75724474077) (nat_lit 549755813888)
  (nat_lit 4371463053773) (nat_lit 1717986918400000)
  (@p130511 (nat_lit 4308819113937) (nat_lit 1717986918400000) true (nat_lit 49854635013)
    (nat_lit 1099511627776) (nat_lit 8603957880999) (nat_lit 3435973836800000)
    (p129097 (nat_lit 38) (nat_lit 39) (Eq.refl true) (Eq.refl true))
    p130778)
  (p130781 p130818)

noncomputable def p130820 :=
p130819 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130821 :=
p130820 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130822 :=
@Enclosure.Complex.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Complex Complex Complex (@instHPow.{0, 0} Complex Complex Complex.instPow)
    (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 40)) p129095)
  {
    re :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40))))
        (Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
            (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1))))),
    im :=
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40))))
        (@Neg.neg.{0} Real Real.instNeg
          (Real.sin
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
              (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1)))))) }

noncomputable def p130823 :=
BSN.cpow_neg_s_mk
  (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))
  (nat_lit 48711) (nat_lit 1000) (nat_lit 40)
  (@Eq.refl.{1} Real
    (Enclosure.sfrac false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))))
  (Eq.refl true)

noncomputable def p130824 :=
@p130822 true (nat_lit 17709392925) (nat_lit 137438953472) (nat_lit 34635422291)
  (nat_lit 858993459200000) false (nat_lit 100754450475) (nat_lit 1099511627776) (nat_lit 137770392289)
  (nat_lit 3435973836800000) p130823

noncomputable def p130825 :=
@Enclosure.Complex.IsNear.mk
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40))))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40))))
    (@Neg.neg.{0} Real Real.instNeg
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
          (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1)))))))
  true

noncomputable def p130826 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40))))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1)))))
  (nat_lit 165795) (nat_lit 1048576) (nat_lit 1)

noncomputable def p130827 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1)))))
  true (nat_lit 854520) (nat_lit 1048576)

noncomputable def p130828 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 47104383)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  false (nat_lit 47104383) (nat_lit 262144)

noncomputable def p130829 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1))))
  false (nat_lit 809247141919098389637) (nat_lit 4503599627370496000) (nat_lit 48711000048711)

noncomputable def p130830 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
  (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1))) (nat_lit 48711) (nat_lit 1000) (nat_lit 0)
  (nat_lit 1) (nat_lit 16613231958266067) (nat_lit 4503599627370496)

noncomputable def p130831 :=
@p130830 (nat_lit 1000000001) (nat_lit 200000000000000) (nat_lit 809247141919098389637)
  (nat_lit 4503599627370496000) (nat_lit 48711000048711) (nat_lit 200000000000000000)
  (Enclosure.Real.IsNear.const false (nat_lit 48711) (nat_lit 1000))
  (BSN.isNear_log_sfrac (nat_lit 40) (nat_lit 1) (nat_lit 16613231958266067) (nat_lit 4503599627370496)
    (nat_lit 1000000001) (nat_lit 200000000000000) false
    (@p33365 (nat_lit 1000000001000000) (nat_lit 200000000000000000000) (nat_lit 16613231958266067)
      (nat_lit 4503599627370496) (nat_lit 1000000001) (nat_lit 200000000000000)
      (p33370 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130832 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 47104383)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23354171577420214173696))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37778931862957161709568)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130833 :=
BSN.sin_reduce_arg_pos_rat_q2 (nat_lit 47104383) (nat_lit 262144) (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 28) (nat_lit 23354171577420214173696) (nat_lit 37778931862957161709568)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p130834 :=
nat_lit 3105836783422563008261524587308550801

noncomputable def p130835 :=
BSN.cos_dyadic_bound_f (nat_lit 1327530957) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130834 p31541 p130834
  p130834 p31542

noncomputable def p130836 :=
@BSN.binarySplit_of_base (BSN.cosEvenP (nat_lit 1327530957)) (BSN.cosEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130834 p31541 p130834 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130837 :=
p130835 p130834 (nat_lit 854520) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130836 (Eq.refl true))

noncomputable def p130838 :=
@BSN.binarySplit_of_base (BSN.cosOddP (nat_lit 1327530957)) (BSN.cosOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130834 p31542 p130834 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130839 :=
@BSN.cos_arg_round false (nat_lit 854520) (nat_lit 1048576) (nat_lit 23354171577420214173696)
  (nat_lit 37778931862957161709568) (nat_lit 1327530957) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130837 (p130838 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130840 :=
p130832 (nat_lit 854520) (nat_lit 1048576) (nat_lit 28) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130833 BSN.pi_near_15 p130839 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130841 :=
@p130828 (nat_lit 257) (nat_lit 1048576) true (nat_lit 854520) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130829 (nat_lit 200000000000000000) (nat_lit 47104383) (nat_lit 262144) (nat_lit 257)
    (nat_lit 1048576) p130831 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 47104383) (nat_lit 262144))
  (p130840 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130842 :=
@p130826 (nat_lit 1048576) (nat_lit 106815) (nat_lit 131072) (nat_lit 819509) (nat_lit 3276800000)
  (nat_lit 17709392925) (nat_lit 137438953472) (nat_lit 34635422291) (nat_lit 858993459200000)
  (@p33355 (nat_lit 165795) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33360
    (Eq.refl true))
  (@p130827 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 106815) (nat_lit 131072)
    (nat_lit 819509) (nat_lit 3276800000) (p130841 (Eq.refl true))
    (Eq.refl true))

noncomputable def p130843 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (nat_lit 40))))
  (@Neg.neg.{0} Real Real.instNeg
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
        (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1))))))
  (nat_lit 165795) (nat_lit 1048576)

noncomputable def p130844 :=
@p130843 (nat_lit 1) (nat_lit 1048576) (nat_lit 607705) (nat_lit 1048576) (nat_lit 819509)
  (nat_lit 3276800000) (nat_lit 100754450475) (nat_lit 1099511627776) (nat_lit 137770392289) (nat_lit 3435973836800000)
  (@p33355 (nat_lit 165795) (nat_lit 1048576) (nat_lit 1) (nat_lit 1048576) p33360
    (Eq.refl true))

noncomputable def p130845 :=
@Enclosure.Real.IsNear.neg
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1)))))
  true (nat_lit 607705) (nat_lit 1048576)

noncomputable def p130846 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
      (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1)))))
  true (nat_lit 607705) (nat_lit 1048576)

noncomputable def p130847 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false (nat_lit 48711) (nat_lit 1000))
    (Real.log (Enclosure.sfrac false (nat_lit 40) (nat_lit 1))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 47104383)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  false (nat_lit 47104383) (nat_lit 262144)

noncomputable def p130848 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 47104383)) (@Nat.cast.{0} Real Real.instNatCast (nat_lit 262144)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 23354171577420214173696))
    (@Nat.cast.{0} Real Real.instNatCast (nat_lit 37778931862957161709568)))
  (nat_lit 226375608064910080) (nat_lit 72057594037927936) false

noncomputable def p130849 :=
BSN.sin_dyadic_bound_f (nat_lit 1327530957) (nat_lit 2147483648) (nat_lit 2) (nat_lit 1) (nat_lit 1048576)
  (nat_lit 400391) p130834 p31525 p130834
  p130834 p31526

noncomputable def p130850 :=
@BSN.binarySplit_of_base (BSN.sinEvenP (nat_lit 1327530957)) (BSN.sinEvenQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130834 p31525 p130834 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130851 :=
p130849 p130834 (nat_lit 607705) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p130850 (Eq.refl true))

noncomputable def p130852 :=
@BSN.binarySplit_of_base (BSN.sinOddP (nat_lit 1327530957)) (BSN.sinOddQ (nat_lit 2147483648)) (nat_lit 0) (nat_lit 1)
  p130834 p31526 p130834 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p130853 :=
@BSN.sin_arg_round false (nat_lit 607705) (nat_lit 1048576) (nat_lit 23354171577420214173696)
  (nat_lit 37778931862957161709568) (nat_lit 1327530957) (nat_lit 2147483648) (nat_lit 400391) (nat_lit 400000)
  (p130851 (p130852 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p130854 :=
p130848 (nat_lit 607705) (nat_lit 1048576) (nat_lit 28) (nat_lit 1000000000000000) (nat_lit 400000)
  (nat_lit 200000) p130833 BSN.pi_near_15 p130853 (Eq.refl true)
  (Eq.refl true)

noncomputable def p130855 :=
@p130847 (nat_lit 257) (nat_lit 1048576) true (nat_lit 607705) (nat_lit 1048576) (nat_lit 1)
  (nat_lit 200000)
  (@p130829 (nat_lit 200000000000000000) (nat_lit 47104383) (nat_lit 262144) (nat_lit 257)
    (nat_lit 1048576) p130831 (Eq.refl true))
  (Enclosure.sfrac_false_div (nat_lit 47104383) (nat_lit 262144))
  (p130854 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p130856 :=
p130844
  (@p130845 (nat_lit 819509) (nat_lit 3276800000)
    (@p130846 (nat_lit 52448576) (nat_lit 209715200000) (nat_lit 607705) (nat_lit 1048576)
      (nat_lit 819509) (nat_lit 3276800000) (p130855 (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p130857 :=
@p130825 (nat_lit 17709392925) (nat_lit 137438953472) (nat_lit 34635422291) (nat_lit 858993459200000)
  false (nat_lit 100754450475) (nat_lit 1099511627776) (nat_lit 137770392289) (nat_lit 3435973836800000)
  (p130842 (Eq.refl true)) p130856

noncomputable def p130858 :=
@p130506 true (nat_lit 27869594831161971965952) (nat_lit 50694497679) (nat_lit 1099511627776)
  (nat_lit 1776139299967) (nat_lit 687194767360000)
  (@p130507 (nat_lit 8757391860671) (nat_lit 3435973836800000) true (nat_lit 75724474077)
    (nat_lit 549755813888) (nat_lit 4371463053773) (nat_lit 1717986918400000)
    (p129097 (nat_lit 39) (nat_lit 40) (Eq.refl true) (Eq.refl true))
    p130821)
  (p130824 p130857)

noncomputable def p130859 :=
p130858 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p130860 :=
p130859 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d1200 : p130502 (nat_lit 687194767360000) :=
@p130503 (nat_lit 1779186709967) (nat_lit 687194767360000) true (nat_lit 50694497679)
  (nat_lit 1099511627776) (nat_lit 1776139299967) (nat_lit 687194767360000)
  (p129097 (nat_lit 40) (nat_lit 41) (Eq.refl true) (Eq.refl true))
  p130860

end RHHeight1000.EMHead40At48711

theorem localSolutionEmHead40 : let z : ℂ := ∑ n ∈ Finset.Ico (1 : ℕ) 41,
      (n : ℂ) ^ (-((1 : ℂ) / 2 + Complex.I * (((48711 : ℝ) / 1000 : ℝ) : ℂ)))
  |z.re - (612813288183 : ℝ) / 1099511627776| ≤ (1779186709967 : ℝ) / 687194767360000 ∧
  |z.im + (50694497679 : ℝ) / 1099511627776| ≤ (1776139299967 : ℝ) / 687194767360000 := by
  simpa [BSN.headSumC, Enclosure.Complex.IsNear, Enclosure.Real.IsNear, Enclosure.sfrac, sub_neg_eq_add] using (show Enclosure.Complex.IsNear
  (BSN.headSumC
    (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
      (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex
        (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
        (@OfNat.ofNat.{0} Complex (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
        ↑(Enclosure.sfrac Bool.false (@OfNat.ofNat.{0} Nat (nat_lit 48711) (instOfNatNat (nat_lit 48711)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000))))))
    (nat_lit 41))
  Bool.false (nat_lit 612813288183) (nat_lit 1099511627776) (nat_lit 1779186709967) (nat_lit 687194767360000) Bool.true
  (nat_lit 50694497679) (nat_lit 1099511627776) (nat_lit 1776139299967) (nat_lit 687194767360000) from RHHeight1000.EMHead40At48711.d1200)

theorem RHHeight1000.em_t48711_head40_enclosure : let z : ℂ := ∑ n ∈ Finset.Ico (1 : ℕ) 41,
      (n : ℂ) ^ (-((1 : ℂ) / 2 + Complex.I * (((48711 : ℝ) / 1000 : ℝ) : ℂ)))
  |z.re - (612813288183 : ℝ) / 1099511627776| ≤ (1779186709967 : ℝ) / 687194767360000 ∧
  |z.im + (50694497679 : ℝ) / 1099511627776| ≤ (1776139299967 : ℝ) / 687194767360000 := localSolutionEmHead40
#print axioms RHHeight1000.em_t48711_head40_enclosure

theorem solution : let z : ℂ := ∑ n ∈ Finset.Ico (1 : ℕ) 41,
      (n : ℂ) ^ (-((1 : ℂ) / 2 + Complex.I * (((48711 : ℝ) / 1000 : ℝ) : ℂ)))
  |z.re - (612813288183 : ℝ) / 1099511627776| ≤ (1779186709967 : ℝ) / 687194767360000 ∧
  |z.im + (50694497679 : ℝ) / 1099511627776| ≤ (1776139299967 : ℝ) / 687194767360000 := RHHeight1000.em_t48711_head40_enclosure
#print axioms solution
