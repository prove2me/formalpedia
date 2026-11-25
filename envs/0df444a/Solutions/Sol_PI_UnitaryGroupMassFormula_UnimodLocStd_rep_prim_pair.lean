-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_prim_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:51.86005+00:00
-- url     : https://prove2.me/submissions/af0c960a-f435-4efe-aa7d-637835ab8278

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepPrimPair
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_coord
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_fvec_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_omega1
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_omega2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀) :
    ∃ xt : m → ℂ, xt ∈ Λ ∧ (∀ j ∈ T, xt j = 0) ∧ ∃ yv : m → ℂ, yv ∈ Λ ∧ ∃ c₂ : ℤ,
      (stdH (cmL a b d ha hd lam hlam) m xt yv).im = c₂ ∧ ¬ (l : ℤ) ∣ c₂ := by
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := h
  set L := cmL a b d ha hd lam hlam with hL
  set f := fvec a b d lam x y i₀ with hfdef
  have hfstd : f ∈ stdLat L m := rep_fvec_mem a b d ha hd lam hlam m x y i₀
  unfold relIdx at h1 h2
  set Df := (Λ.relIndex (stdLat L m)).factorial with hDf
  set Nf := ((stdLat L m).relIndex Λ).factorial with hNf
  have hDfΛ : Df • f ∈ Λ :=
    (AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd h2 hfstd
      (fun j hj hle => Nat.dvd_factorial hj hle)).1
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hlam0 := hlam

  set P : ℕ → Prop := fun j => ((l : ℂ) ^ j)⁻¹ • (Df • f) ∈ Λ with hPdef
  have hex : ∃ j, ¬ P j := by
    by_contra hall
    push_neg at hall
    set K : ℕ := Nf * Df with hK
    have hK0 : K ≠ 0 := Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
    have hdvd : ∀ j : ℕ, (l : ℤ) ^ j ∣ K * x ∧ (l : ℤ) ^ j ∣ K * y := by
      intro j
      have hmem : Nf • (((l : ℂ) ^ j)⁻¹ • (Df • f)) ∈ stdLat L m :=
        (AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd h1 (hall j)
          (fun j hj hle => Nat.dvd_factorial hj hle)).1
      obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp (hmem i₀ (Set.mem_univ i₀))
      rw [rep_omega1, rep_omega2] at hpq
      simp only [hfdef, fvec, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, smul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at hpq
      have hlj : ((l : ℂ) ^ j) ≠ 0 := pow_ne_zero _ hl0
      have e : ((p : ℝ) : ℂ) * a + ((q : ℝ) : ℂ) * cmTheta b d =
          (((K * x : ℤ) / (l : ℝ) ^ j : ℝ) : ℂ) * a + (((K * y : ℤ) / (l : ℝ) ^ j : ℝ) : ℂ) * cmTheta b d := by
        apply mul_left_cancel₀ hlam
        push_cast
        rw [hK]; push_cast
        linear_combination hpq
      obtain ⟨ep, eq'⟩ := rep_coord a ha b d hd _ _ _ _ e
      have hlj' : ((l : ℝ) ^ j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
      refine ⟨⟨p, ?_⟩, ⟨q, ?_⟩⟩
      · rw [eq_div_iff hlj'] at ep
        have : ((K * x : ℤ) : ℝ) = ((l ^ j * p : ℤ) : ℝ) := by push_cast at ep ⊢; linear_combination -ep
        exact_mod_cast this
      · rw [eq_div_iff hlj'] at eq'
        have : ((K * y : ℤ) : ℝ) = ((l ^ j * q : ℤ) : ℝ) := by push_cast at eq' ⊢; linear_combination -eq'
        exact_mod_cast this
    set J := K * (x.natAbs + y.natAbs) + 1
    have hJ : K * (x.natAbs + y.natAbs) < l ^ J :=
      lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.lt_pow_self hl.one_lt).le)
    have hx0 : K * x = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd J).1
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp only [Int.natAbs_natCast]
      calc K * x.natAbs ≤ K * (x.natAbs + y.natAbs) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
        _ < l ^ J := hJ
    have hy0 : K * y = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd J).2
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp only [Int.natAbs_natCast]
      calc K * y.natAbs ≤ K * (x.natAbs + y.natAbs) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
        _ < l ^ J := hJ
    have hK0' : (K : ℤ) ≠ 0 := by exact_mod_cast hK0
    have hx : x = 0 := (mul_eq_zero.mp hx0).resolve_left hK0'
    have hy : y = 0 := (mul_eq_zero.mp hy0).resolve_left hK0'
    apply hQ; rw [hx, hy]; simp
  classical
  set j₁ := Nat.find hex with hj₁
  have hP0 : P 0 := by simp only [hPdef, pow_zero, inv_one, one_smul]; exact hDfΛ
  have hj₁0 : j₁ ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hj₁, h0] at this
    exact this hP0
  have hPprev : P (j₁ - 1) := by
    have := Nat.find_min hex (show j₁ - 1 < Nat.find hex by omega)
    simpa using this
  have hPj : ¬ P j₁ := Nat.find_spec hex
  set xt := ((l : ℂ) ^ (j₁ - 1))⁻¹ • (Df • f) with hxt
  have hxtΛ : xt ∈ Λ := hPprev
  have hxtT : ∀ j ∈ T, xt j = 0 := by
    intro j hj
    have hne : j ≠ i₀ := by rintro rfl; exact hi₀ hj
    simp [hxt, hfdef, fvec, Pi.single_apply, hne]
  have hdiv : ((l : ℂ)⁻¹) • xt ∉ Λ := by
    rw [hxt, smul_smul, ← mul_inv, ← pow_succ', show j₁ - 1 + 1 = j₁ by omega]
    exact hPj
  refine ⟨xt, hxtΛ, hxtT, ?_⟩
  have hnd : ¬ ∀ yv ∈ Λ, ∃ k : ℤ, altE (stdH L m) ((l : ℂ)⁻¹ • xt) yv = k := by
    intro hall
    apply hdiv
    have : ((l : ℂ)⁻¹ • xt) ∈ dualLat (stdH L m) Λ := hall
    rw [hΛ] at this
    exact this
  push_neg at hnd
  obtain ⟨yv, hyv, hyk⟩ := hnd
  have hxtd : xt ∈ dualLat (stdH L m) Λ := by rw [hΛ]; exact hxtΛ
  obtain ⟨c₂, hc₂⟩ := hxtd yv hyv
  refine ⟨yv, hyv, c₂, hc₂, ?_⟩
  rintro ⟨t, rfl⟩
  apply hyk t
  simp only [altE] at hc₂ ⊢
  have e : (stdH L m ((l : ℂ)⁻¹ • xt) yv) = (((l : ℝ)⁻¹ : ℝ) : ℂ) * stdH L m xt yv := by
    simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]; push_cast; ring
  rw [e, Complex.im_ofReal_mul, hc₂]
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne_zero
  push_cast
  field_simp
end PI.UnitaryGroupMassFormula.UnimodLocStd
