-- Prove2me | solution 1 for RHHeight1000.em_t48711_head24_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T10:09:14.818496+00:00
-- url     : https://prove2.me/submissions/9f3653fa-90b5-4bbe-9be9-6d0d08817742

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

theorem solution : let z : ℂ := ∑ n ∈ Finset.Ico (1 : ℕ) 25,
      (n : ℂ) ^ (-((1 : ℂ) / 2 + Complex.I * (((48711 : ℝ) / 1000 : ℝ) : ℂ)))
  |z.re - (39429631493 : ℝ) / 68719476736| ≤ (128710925751 : ℝ) / 68719476736000 ∧
  |z.im - (20347977125 : ℝ) / 549755813888| ≤ (128436149751 : ℝ) / 68719476736000 := RHHeight1000.em_t48711_head24_enclosure
#print axioms solution
