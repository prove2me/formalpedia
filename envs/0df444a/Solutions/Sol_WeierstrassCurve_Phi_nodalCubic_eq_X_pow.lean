-- Prove2me | solution 1 for WeierstrassCurve.Phi_nodalCubic_eq_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c8402c3b-32df-569f-8806-08c31a75e720

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Phi_nodalCubic_eq_X_pow

set_option autoImplicit false

universe u

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_Phi_nodalCubic_eq_X_pow.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "preΨ'_one preΨ'_even preΨ'_four map preΨ'_two Φ_ofNat Ψ₃ map_Φ b₂ preΨ'_zero Φ_zero mk Ψ₂Sq preΨ'_odd preΨ₄ preΨ' ψ₂ b₆ b₈ preΨ'_three Φ_neg j b₄"
namespace NodalCubic
p2m_open "WeierstrassCurve"

noncomputable def N (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨1, 0, 0, 0, 0⟩

theorem N_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : (N R).map f = N S := by
  simp [N, WeierstrassCurve.map]

noncomputable def xs : ℤ[X] := X * (1 + X)

noncomputable def ts : ℤ[X] := X * (1 + X) * (1 + 2 * X)

noncomputable def gs (n : ℕ) : ℤ[X] := (1 + X) ^ n - X ^ n

def e (n : ℕ) : ℕ := n * (n - 1) / 2

noncomputable def ψs (n : ℕ) : ℤ[X] := X ^ e n * (1 + X) ^ e n * gs n

noncomputable def tpow (n : ℕ) : ℤ[X] := if Even n then ts else 1

theorem e_two_mul (q : ℕ) : e (2 * q) = q * (2 * q - 1) := by
  unfold e
  rcases q with _ | q
  · simp
  · rw [show 2 * (q + 1) * (2 * (q + 1) - 1) = 2 * ((q + 1) * (2 * (q + 1) - 1)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos

theorem e_two_mul_add_one (q : ℕ) : e (2 * q + 1) = q * (2 * q + 1) := by
  unfold e
  rw [Nat.add_sub_cancel, show (2 * q + 1) * (2 * q) = 2 * (q * (2 * q + 1)) by ring]
  exact Nat.mul_div_cancel_left _ two_pos

theorem e1 (j : ℕ) : e (2 * j + 1) = j * (2 * j + 1) := e_two_mul_add_one j
theorem e2 (j : ℕ) : e (2 * j + 2) = (j + 1) * (2 * j + 1) := by
  rw [show 2 * j + 2 = 2 * (j + 1) by ring, e_two_mul]; congr 1
theorem e3 (j : ℕ) : e (2 * j + 3) = (j + 1) * (2 * j + 3) := by
  rw [show 2 * j + 3 = 2 * (j + 1) + 1 by ring, e_two_mul_add_one]
theorem e4 (j : ℕ) : e (2 * j + 4) = (j + 2) * (2 * j + 3) := by
  rw [show 2 * j + 4 = 2 * (j + 2) by ring, e_two_mul]; congr 1
theorem e5 (j : ℕ) : e (2 * j + 5) = (j + 2) * (2 * j + 5) := by
  rw [show 2 * j + 5 = 2 * (j + 2) + 1 by ring, e_two_mul_add_one]
theorem e6 (j : ℕ) : e (2 * j + 6) = (j + 3) * (2 * j + 5) := by
  rw [show 2 * j + 6 = 2 * (j + 3) by ring, e_two_mul]; congr 1
theorem e45 (j : ℕ) : e (4 * j + 5) = (2 * j + 2) * (4 * j + 5) := by
  rw [show 4 * j + 5 = 2 * (2 * j + 2) + 1 by ring, e_two_mul_add_one]
theorem e46 (j : ℕ) : e (4 * j + 6) = (2 * j + 3) * (4 * j + 5) := by
  rw [show 4 * j + 6 = 2 * (2 * j + 3) by ring, e_two_mul, show 2 * (2 * j + 3) - 1 = 4 * j + 5 by omega]
theorem e47 (j : ℕ) : e (4 * j + 7) = (2 * j + 3) * (4 * j + 7) := by
  rw [show 4 * j + 7 = 2 * (2 * j + 3) + 1 by ring, e_two_mul_add_one]
theorem e48 (j : ℕ) : e (4 * j + 8) = (2 * j + 4) * (4 * j + 7) := by
  rw [show 4 * j + 8 = 2 * (2 * j + 4) by ring, e_two_mul, show 2 * (2 * j + 4) - 1 = 4 * j + 7 by omega]

theorem tpow1 (j : ℕ) : tpow (2 * j + 1) = 1 := if_neg (Nat.not_even_iff_odd.mpr ⟨j, rfl⟩)
theorem tpow2 (j : ℕ) : tpow (2 * j + 2) = ts := if_pos ⟨j + 1, by ring⟩
theorem tpow3 (j : ℕ) : tpow (2 * j + 3) = 1 := if_neg (Nat.not_even_iff_odd.mpr ⟨j + 1, by ring⟩)
theorem tpow4 (j : ℕ) : tpow (2 * j + 4) = ts := if_pos ⟨j + 2, by ring⟩
theorem tpow5 (j : ℕ) : tpow (2 * j + 5) = 1 := if_neg (Nat.not_even_iff_odd.mpr ⟨j + 2, by ring⟩)
theorem tpow6 (j : ℕ) : tpow (2 * j + 6) = ts := if_pos ⟨j + 3, by ring⟩

theorem ψs_odd_even (j : ℕ) :
    ψs (4 * j + 5) = ψs (2 * j + 4) * ψs (2 * j + 2) ^ 3 - ψs (2 * j + 1) * ψs (2 * j + 3) ^ 3 := by
  simp only [ψs, e1, e2, e3, e4, e45, xs, gs]; ring

theorem ψs_odd_odd (j : ℕ) :
    ψs (4 * j + 7) = ψs (2 * j + 5) * ψs (2 * j + 3) ^ 3 - ψs (2 * j + 2) * ψs (2 * j + 4) ^ 3 := by
  simp only [ψs, e2, e3, e4, e5, e47, xs, gs]; ring

theorem ψs_even_even (j : ℕ) :
    ψs (4 * j + 6) * ts =
      ψs (2 * j + 2) ^ 2 * ψs (2 * j + 3) * ψs (2 * j + 5)
        - ψs (2 * j + 1) * ψs (2 * j + 3) * ψs (2 * j + 4) ^ 2 := by
  simp only [ψs, e1, e2, e3, e4, e5, e46, xs, gs, ts]; ring

theorem ψs_even_odd (j : ℕ) :
    ψs (4 * j + 8) * ts =
      ψs (2 * j + 3) ^ 2 * ψs (2 * j + 4) * ψs (2 * j + 6)
        - ψs (2 * j + 2) * ψs (2 * j + 4) * ψs (2 * j + 5) ^ 2 := by
  simp only [ψs, e2, e3, e4, e5, e6, e48, xs, gs, ts]; ring

theorem Φs_odd (j : ℕ) :
    xs * ψs (2 * j + 3) ^ 2 - ψs (2 * j + 4) * ψs (2 * j + 2) =
      X ^ ((2 * j + 3) ^ 2) * (1 + X) ^ ((2 * j + 3) ^ 2) := by
  simp only [ψs, e2, e3, e4, xs, gs]; ring

theorem Φs_even (j : ℕ) :
    xs * ψs (2 * j + 2) ^ 2 - ψs (2 * j + 3) * ψs (2 * j + 1) =
      X ^ ((2 * j + 2) ^ 2) * (1 + X) ^ ((2 * j + 2) ^ 2) := by
  simp only [ψs, e1, e2, e3, xs, gs]; ring

noncomputable def E (n : ℕ) : ℤ[X] := ((N ℤ).preΨ' n).comp xs

theorem N_b₂ : (N ℤ).b₂ = 1 := by simp [N, b₂]
theorem N_b₄ : (N ℤ).b₄ = 0 := by simp [N, b₄]
theorem N_b₆ : (N ℤ).b₆ = 0 := by simp [N, b₆]
theorem N_b₈ : (N ℤ).b₈ = 0 := by simp [N, b₈]

theorem Ψ₂Sq_N : (N ℤ).Ψ₂Sq = 4 * X ^ 3 + X ^ 2 := by
  simp [Ψ₂Sq, N_b₂, N_b₄, N_b₆]

theorem Ψ₃_N : (N ℤ).Ψ₃ = 3 * X ^ 4 + X ^ 3 := by
  simp [Ψ₃, N_b₂, N_b₄, N_b₆, N_b₈]

theorem preΨ₄_N : (N ℤ).preΨ₄ = 2 * X ^ 6 + X ^ 5 := by
  simp [preΨ₄, N_b₂, N_b₄, N_b₆, N_b₈]

theorem Ψ₂Sq_comp : (N ℤ).Ψ₂Sq.comp xs = ts ^ 2 := by
  rw [Ψ₂Sq_N]
  simp only [add_comp, mul_comp, pow_comp, X_comp, ofNat_comp, xs, ts]
  ring

theorem E3 : E 3 = ψs 3 := by
  rw [E, preΨ'_three, Ψ₃_N]
  simp only [add_comp, mul_comp, pow_comp, X_comp, ofNat_comp, xs, ψs, gs, show e 3 = 3 by decide]
  ring

theorem E4 : E 4 * ts = ψs 4 := by
  rw [E, preΨ'_four, preΨ₄_N]
  simp only [add_comp, mul_comp, pow_comp, X_comp, ofNat_comp, xs, ts, ψs, gs, show e 4 = 6 by decide]
  ring

theorem ts_ne_zero : ts ≠ 0 := by
  intro h
  have := congrArg (eval 1) h
  norm_num [ts] at this

theorem claimA (n : ℕ) : E n * tpow n = ψs n := by
  induction n using normEDSRec' with
  | zero => simp [E, tpow, ψs, gs, preΨ'_zero]
  | one => simp [E, tpow, ψs, gs, e, preΨ'_one]
  | two =>
    have ht : tpow 2 = ts := if_pos even_two
    have h2 : e 2 = 1 := by decide
    rw [ht, E, preΨ'_two, one_comp, one_mul]
    simp only [ψs, gs, ts, h2]
    ring
  | three => rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, tpow1, mul_one]; exact E3
  | four => rw [show (4 : ℕ) = 2 * 1 + 2 from rfl, tpow2]; exact E4
  | even m ih =>
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    ·
      have h1 := ih (2 * j + 1) (by omega); rw [tpow1, mul_one] at h1
      have h2 := ih (2 * j + 2) (by omega); rw [tpow2] at h2
      have h3 := ih (2 * j + 3) (by omega); rw [tpow3, mul_one] at h3
      have h4 := ih (2 * j + 4) (by omega); rw [tpow4] at h4
      have h5 := ih (2 * j + 5) (by omega); rw [tpow5, mul_one] at h5
      have hrec := (N ℤ).preΨ'_even (2 * j)
      have key : E (2 * (2 * j + 3)) * ts * ts =
          (E (2 * j + 2) * ts) ^ 2 * E (2 * j + 3) * E (2 * j + 5)
            - E (2 * j + 1) * E (2 * j + 3) * (E (2 * j + 4) * ts) ^ 2 := by
        rw [E, hrec]; simp only [sub_comp, mul_comp, pow_comp, E]; ring_nf
      rw [h1, h2, h3, h4, h5, show 2 * (2 * j + 3) = 4 * j + 6 by ring, ← ψs_even_even] at key
      rw [show 2 * (2 * j + 3) = 2 * (2 * j + 2) + 2 by ring, tpow2, show 2 * (2 * j + 2) + 2 = 4 * j + 6 by ring]
      exact mul_right_cancel₀ ts_ne_zero key
    ·
      have h2 := ih (2 * j + 2) (by omega); rw [tpow2] at h2
      have h3 := ih (2 * j + 3) (by omega); rw [tpow3, mul_one] at h3
      have h4 := ih (2 * j + 4) (by omega); rw [tpow4] at h4
      have h5 := ih (2 * j + 5) (by omega); rw [tpow5, mul_one] at h5
      have h6 := ih (2 * j + 6) (by omega); rw [tpow6] at h6
      have hrec := (N ℤ).preΨ'_even (2 * j + 1)
      have key : E (2 * (2 * j + 1 + 3)) * ts * ts =
          E (2 * j + 3) ^ 2 * (E (2 * j + 4) * ts) * (E (2 * j + 6) * ts)
            - (E (2 * j + 2) * ts) * (E (2 * j + 4) * ts) * E (2 * j + 5) ^ 2 := by
        rw [E, hrec]; simp only [sub_comp, mul_comp, pow_comp, E]; ring_nf
      rw [h2, h3, h4, h5, h6, show 2 * (2 * j + 1 + 3) = 4 * j + 8 by ring, ← ψs_even_odd] at key
      rw [show 2 * (2 * j + 1 + 3) = 2 * (2 * j + 3) + 2 by ring, tpow2, show 2 * (2 * j + 3) + 2 = 4 * j + 8 by ring]
      exact mul_right_cancel₀ ts_ne_zero key
  | odd m ih =>
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    ·
      have h1 := ih (2 * j + 1) (by omega); rw [tpow1, mul_one] at h1
      have h2 := ih (2 * j + 2) (by omega); rw [tpow2] at h2
      have h3 := ih (2 * j + 3) (by omega); rw [tpow3, mul_one] at h3
      have h4 := ih (2 * j + 4) (by omega); rw [tpow4] at h4
      have hrec := (N ℤ).preΨ'_odd (2 * j)
      rw [if_pos (even_two_mul j), if_pos (even_two_mul j), mul_one] at hrec
      have key : E (2 * (2 * j + 2) + 1) =
          (E (2 * j + 4) * ts) * (E (2 * j + 2) * ts) ^ 3 - E (2 * j + 1) * E (2 * j + 3) ^ 3 := by
        rw [E, hrec]; simp only [sub_comp, mul_comp, pow_comp, Ψ₂Sq_comp, E]; ring_nf
      rw [h1, h2, h3, h4, ← ψs_odd_even] at key
      rw [tpow1, mul_one, key]
      congr 1; ring
    ·
      have h2 := ih (2 * j + 2) (by omega); rw [tpow2] at h2
      have h3 := ih (2 * j + 3) (by omega); rw [tpow3, mul_one] at h3
      have h4 := ih (2 * j + 4) (by omega); rw [tpow4] at h4
      have h5 := ih (2 * j + 5) (by omega); rw [tpow5, mul_one] at h5
      have hrec := (N ℤ).preΨ'_odd (2 * j + 1)
      have hodd : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr ⟨j, rfl⟩
      rw [if_neg hodd, if_neg hodd, mul_one] at hrec
      have key : E (2 * (2 * j + 1 + 2) + 1) =
          E (2 * j + 5) * E (2 * j + 3) ^ 3 - (E (2 * j + 2) * ts) * (E (2 * j + 4) * ts) ^ 3 := by
        rw [E, hrec]; simp only [sub_comp, mul_comp, pow_comp, Ψ₂Sq_comp, E]; ring_nf
      rw [h2, h3, h4, h5, ← ψs_odd_odd] at key
      rw [tpow1, mul_one, key]
      congr 1; ring

theorem E_odd' (j : ℕ) : E (2 * j + 1) = ψs (2 * j + 1) := by
  have := claimA (2 * j + 1); rwa [tpow1, mul_one] at this
theorem E_even' (j : ℕ) : E (2 * j + 2) * ts = ψs (2 * j + 2) := by
  have := claimA (2 * j + 2); rwa [tpow2] at this

theorem Φ_comp_succ (n : ℕ) :
    ((N ℤ).Φ ((n : ℤ) + 1)).comp xs = X ^ ((n + 1) ^ 2) * (1 + X) ^ ((n + 1) ^ 2) := by
  rw [Φ_ofNat]
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · rw [if_pos (even_two_mul j), if_pos (even_two_mul j), mul_one]
    rcases j with _ | j
    ·
      simp only [mul_zero, zero_add, preΨ'_one, preΨ'_zero, mul_zero, zero_mul, sub_zero, one_pow,
        mul_one, X_comp, xs]
      ring
    ·
      have a : ((N ℤ).preΨ' (2 * (j + 1) + 1)).comp xs = ψs (2 * j + 3) := by
        rw [show 2 * (j + 1) + 1 = 2 * (j + 1) + 1 from rfl]; exact E_odd' (j + 1)
      have b : ((N ℤ).preΨ' (2 * (j + 1) + 2)).comp xs * ts = ψs (2 * j + 4) := E_even' (j + 1)
      have c : ((N ℤ).preΨ' (2 * (j + 1))).comp xs * ts = ψs (2 * j + 2) := by
        rw [show 2 * (j + 1) = 2 * j + 2 by ring]; exact E_even' j
      have key : (X * (N ℤ).preΨ' (2 * (j + 1) + 1) ^ 2 -
            (N ℤ).preΨ' (2 * (j + 1) + 2) * (N ℤ).preΨ' (2 * (j + 1)) * (N ℤ).Ψ₂Sq).comp xs =
          xs * ((N ℤ).preΨ' (2 * (j + 1) + 1)).comp xs ^ 2 -
            (((N ℤ).preΨ' (2 * (j + 1) + 2)).comp xs * ts) * (((N ℤ).preΨ' (2 * (j + 1))).comp xs * ts) := by
        simp only [sub_comp, mul_comp, pow_comp, X_comp, Ψ₂Sq_comp]; ring
      rw [key, a, b, c, Φs_odd j]
      ring
  ·
    have hodd : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr ⟨j, rfl⟩
    rw [if_neg hodd, if_neg hodd, mul_one]
    have a : ((N ℤ).preΨ' (2 * j + 1 + 1)).comp xs * ts = ψs (2 * j + 2) := E_even' j
    have b : ((N ℤ).preΨ' (2 * j + 1 + 2)).comp xs = ψs (2 * j + 3) := E_odd' (j + 1)
    have c : ((N ℤ).preΨ' (2 * j + 1)).comp xs = ψs (2 * j + 1) := E_odd' j
    have key : (X * (N ℤ).preΨ' (2 * j + 1 + 1) ^ 2 * (N ℤ).Ψ₂Sq -
          (N ℤ).preΨ' (2 * j + 1 + 2) * (N ℤ).preΨ' (2 * j + 1)).comp xs =
        xs * (((N ℤ).preΨ' (2 * j + 1 + 1)).comp xs * ts) ^ 2 -
          ((N ℤ).preΨ' (2 * j + 1 + 2)).comp xs * ((N ℤ).preΨ' (2 * j + 1)).comp xs := by
      simp only [sub_comp, mul_comp, pow_comp, X_comp, Ψ₂Sq_comp]; ring
    rw [key, a, b, c, Φs_even j]

theorem natDegree_xs : xs.natDegree = 2 := by
  unfold xs; compute_degree!

theorem comp_xs_injective : Function.Injective (fun p : ℤ[X] => p.comp xs) := by
  intro p q h
  have h0 : (p - q).comp xs = 0 := by simp only at h; rw [sub_comp, h, sub_self]
  have hdeg : (p - q).natDegree = 0 := by
    have := natDegree_comp (p := p - q) (q := xs)
    rw [h0, natDegree_zero, natDegree_xs] at this
    omega
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hdeg
  rw [← hc, C_comp] at h0
  rw [← sub_eq_zero, ← hc, h0]

theorem Φ_nat (n : ℕ) : (N ℤ).Φ (n : ℤ) = X ^ (n ^ 2) := by
  rcases n with _ | n
  · simp [Φ_zero]
  · apply comp_xs_injective
    simp only
    rw [Nat.cast_succ, Φ_comp_succ, pow_comp, X_comp, xs, mul_pow]

theorem Φ_int (n : ℤ) : (N ℤ).Φ n = X ^ (n.natAbs ^ 2) := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [Int.natAbs_natCast, Φ_nat]
  · rw [Φ_neg, Int.natAbs_neg, Int.natAbs_natCast, Φ_nat]

theorem Φ_eq (R : Type*) [CommRing R] (n : ℤ) : (N R).Φ n = X ^ (n.natAbs ^ 2) := by
  rw [← N_map (Int.castRingHom R), map_Φ, Φ_int, Polynomial.map_pow, map_X]

end WeierstrassCurve.NodalCubic

theorem solution (R : Type u) [CommRing R] (n : ℤ) :
    (WeierstrassCurve.mk 1 0 0 0 0 : WeierstrassCurve R).Φ n = Polynomial.X ^ (n.natAbs ^ 2) :=
  WeierstrassCurve.NodalCubic.Φ_eq R n

end S_WeierstrassCurve_Phi_nodalCubic_eq_X_pow
end P2MW
export P2MW.S_WeierstrassCurve_Phi_nodalCubic_eq_X_pow (solution)
