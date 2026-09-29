-- Prove2me | solution 1 for PowerSeries.existsUnique_ringHom_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/20dbca0b-0025-5090-858f-675cc6a20b85

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_existsUnique_ringHom_of_isAdicComplete
set_option autoImplicit false

namespace PowerSeries
p2m_export "PowerSeries" "coe_mul mk trunc eval₂_X coeff_coe coeff_C eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc coe_one eval₂_C coe_X ext map C coeff X coe_C coeff_X"
p2m_open "PowerSeries"

variable {A S : Type*} [CommRing A] [CommRing S]

theorem liftOfIsAdicComplete_sum_range_sub_sum_range_mem (J : Ideal S) (θ : A →+* S) (x : S)
    (hx : x ∈ J) (F : PowerSeries A) {m N : ℕ} (h : m ≤ N) :
    (Finset.range N).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) -
      (Finset.range m).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) ∈ J ^ m := by
  rw [← Finset.sum_range_add_sum_Ico _ h, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hi.1 (Ideal.pow_mem_pow hx i))

theorem liftOfIsAdicComplete_eval₂_sub_eval₂_trunc_mem (J : Ideal S) (θ : A →+* S) (x : S)
    (hx : x ∈ J) (P : Polynomial A) (n : ℕ) :
    Polynomial.eval₂ θ x P - Polynomial.eval₂ θ x (PowerSeries.trunc n (P : PowerSeries A)) ∈ J ^ n := by
  have hN : P.natDegree < max n (P.natDegree + 1) := by omega
  rw [Polynomial.eval₂_eq_sum_range' θ hN, PowerSeries.eval₂_trunc_eq_sum_range]
  simpa only [Polynomial.coeff_coe] using
    liftOfIsAdicComplete_sum_range_sub_sum_range_mem J θ x hx (P : PowerSeries A)
      (le_max_left n (P.natDegree + 1))

noncomputable def liftOfIsAdicCompleteAux (J : Ideal S) (θ : A →+* S) (x : S) (hx : x ∈ J) (n : ℕ) :
    PowerSeries A →+* S ⧸ J ^ n where
  toFun F := Ideal.Quotient.mk (J ^ n) (Polynomial.eval₂ θ x (PowerSeries.trunc n F))
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk (J ^ n)), Ideal.Quotient.eq, ← Polynomial.eval₂_one θ x,
      ← Polynomial.coe_one]
    rw [← neg_mem_iff, neg_sub]
    exact liftOfIsAdicComplete_eval₂_sub_eval₂_trunc_mem J θ x hx 1 n
  map_mul' F G := by
    rw [← map_mul, Ideal.Quotient.eq, ← Polynomial.eval₂_mul, ← PowerSeries.trunc_trunc_mul_trunc,
      ← Polynomial.coe_mul, ← neg_mem_iff, neg_sub]
    exact liftOfIsAdicComplete_eval₂_sub_eval₂_trunc_mem J θ x hx _ n
  map_zero' := by simp
  map_add' F G := by simp [Polynomial.eval₂_add]

theorem liftOfIsAdicCompleteAux_apply (J : Ideal S) (θ : A →+* S) (x : S) (hx : x ∈ J) (n : ℕ)
    (F : PowerSeries A) :
    liftOfIsAdicCompleteAux J θ x hx n F =
      Ideal.Quotient.mk (J ^ n) ((Finset.range n).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i)) := by
  simp [liftOfIsAdicCompleteAux, PowerSeries.eval₂_trunc_eq_sum_range]

theorem liftOfIsAdicCompleteAux_compat (J : Ideal S) (θ : A →+* S) (x : S) (hx : x ∈ J) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (liftOfIsAdicCompleteAux J θ x hx n) =
      liftOfIsAdicCompleteAux J θ x hx m := by
  ext F
  simp only [RingHom.comp_apply, liftOfIsAdicCompleteAux_apply, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  exact liftOfIsAdicComplete_sum_range_sub_sum_range_mem J θ x hx F hle

end PowerSeries

namespace PowerSeries p2m_export "PowerSeries" "coe_mul mk trunc eval₂_X coeff_coe coeff_C eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc coe_one eval₂_C coe_X ext map C coeff X coe_C coeff_X" end PowerSeries
p2m_open_scoped "PowerSeries" in
noncomputable def PowerSeries.liftOfIsAdicComplete {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) : PowerSeries A →+* S :=
  IsAdicComplete.liftRingHom J (PowerSeries.liftOfIsAdicCompleteAux J θ x hx)
    (fun hle => PowerSeries.liftOfIsAdicCompleteAux_compat J θ x hx hle)

p2m_open_scoped "PowerSeries" in

theorem PowerSeries.liftOfIsAdicComplete_sub_sum_mem {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) (F : PowerSeries A) (n : ℕ) :
    PowerSeries.liftOfIsAdicComplete J θ x hx F -
      (Finset.range n).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) ∈ J ^ n := by
  rw [← Ideal.Quotient.eq, ← PowerSeries.liftOfIsAdicCompleteAux_apply J θ x hx]
  exact IsAdicComplete.mk_liftRingHom J _ _ n F

namespace PowerSeries
p2m_export "PowerSeries" "coe_mul mk trunc eval₂_X coeff_coe coeff_C eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc coe_one eval₂_C coe_X ext map C coeff X coe_C coeff_X"
p2m_open "PowerSeries"

variable {A S : Type*} [CommRing A] [CommRing S]

theorem liftOfIsAdicComplete_eq_of_forall_sub_mem (J : Ideal S) [IsHausdorff J S] {a b : S}
    (h : ∀ n, a - b ∈ J ^ n) : a = b := by
  refine sub_eq_zero.mp (IsHausdorff.haus ‹_› _ fun n => ?_)
  rw [SModEq.zero]
  simpa [smul_eq_mul, Ideal.mul_top] using h n

theorem liftOfIsAdicComplete_coe (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J)
    (P : Polynomial A) :
    PowerSeries.liftOfIsAdicComplete J θ x hx (P : PowerSeries A) = Polynomial.eval₂ θ x P := by
  refine liftOfIsAdicComplete_eq_of_forall_sub_mem J fun n => ?_
  have h1 := PowerSeries.liftOfIsAdicComplete_sub_sum_mem J θ x hx (P : PowerSeries A) n
  have h2 := liftOfIsAdicComplete_eval₂_sub_eval₂_trunc_mem J θ x hx P n
  rw [PowerSeries.eval₂_trunc_eq_sum_range] at h2
  simpa using sub_mem h1 h2

end PowerSeries

p2m_open_scoped "PowerSeries" in
theorem PowerSeries.liftOfIsAdicComplete_C {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) (a : A) :
    PowerSeries.liftOfIsAdicComplete J θ x hx (PowerSeries.C a) = θ a := by
  rw [← Polynomial.coe_C, PowerSeries.liftOfIsAdicComplete_coe, Polynomial.eval₂_C]

p2m_open_scoped "PowerSeries" in
theorem PowerSeries.liftOfIsAdicComplete_X {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) :
    PowerSeries.liftOfIsAdicComplete J θ x hx PowerSeries.X = x := by
  rw [← Polynomial.coe_X, PowerSeries.liftOfIsAdicComplete_coe, Polynomial.eval₂_X]

p2m_open_scoped "PowerSeries" in

theorem PowerSeries.eq_liftOfIsAdicComplete {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) (φ : PowerSeries A →+* S)
    (hC : ∀ a, φ (PowerSeries.C a) = θ a) (hX : φ PowerSeries.X = x)
    (hcont : ∀ F n, φ F - (Finset.range n).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) ∈ J ^ n) :
    φ = PowerSeries.liftOfIsAdicComplete J θ x hx := by
  have := And.intro hC hX; clear this
  refine RingHom.ext fun F => PowerSeries.liftOfIsAdicComplete_eq_of_forall_sub_mem J fun n => ?_
  simpa using sub_mem (hcont F n) (PowerSeries.liftOfIsAdicComplete_sub_sum_mem J θ x hx F n)

theorem solution {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) :
    ∃! φ : PowerSeries A →+* S,
      ∀ (F : PowerSeries A) (n : ℕ),
        φ F - (Finset.range n).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) ∈ J ^ n := by
  refine ⟨PowerSeries.liftOfIsAdicComplete J θ x hx, PowerSeries.liftOfIsAdicComplete_sub_sum_mem J θ x hx, ?_⟩
  intro φ hφ
  apply PowerSeries.eq_liftOfIsAdicComplete J θ x hx φ ?_ ?_ hφ
  · intro a
    rw [← sub_eq_zero]
    apply IsHausdorff.haus (inferInstance : IsHausdorff J S)
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have h := hφ (PowerSeries.C a) (n + 1)
    rw [Finset.sum_range_succ', Finset.sum_eq_zero] at h
    · simpa using Ideal.pow_le_pow_right (Nat.le_succ n) h
    · intro i _
      rw [PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero i), map_zero, zero_mul]
  · rw [← sub_eq_zero]
    apply IsHausdorff.haus (inferInstance : IsHausdorff J S)
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have h := hφ PowerSeries.X (n + 2)
    rw [Finset.sum_eq_single 1] at h
    · simpa using Ideal.pow_le_pow_right (by omega : n ≤ n + 2) h
    · intro i _ hi
      rw [PowerSeries.coeff_X, if_neg hi, map_zero, zero_mul]
    · intro h1; exfalso; apply h1; simp

end S_PowerSeries_existsUnique_ringHom_of_isAdicComplete
end P2MW
export P2MW.S_PowerSeries_existsUnique_ringHom_of_isAdicComplete (solution)
