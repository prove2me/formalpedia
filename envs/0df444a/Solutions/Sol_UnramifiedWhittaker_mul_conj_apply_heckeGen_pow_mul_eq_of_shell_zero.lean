-- Prove2me | solution 1 for UnramifiedWhittaker.mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/791b2155-dfb5-5755-b573-acb277ee8993

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_UnramifiedWhittaker_apply_mul_placeEmbed_diagZ_eq_mul_torusFactor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero

set_option autoImplicit false

open Matrix
open IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace UnramW17

theorem conj_heckeRecursionSeq (N : ℕ) (lam om : ℂ) (m : ℕ) :
    (starRingEnd ℂ) (heckeRecursionSeq (N : ℂ) lam om m) =
      heckeRecursionSeq (N : ℂ) ((starRingEnd ℂ) lam) ((starRingEnd ℂ) om) m := by
  suffices H : (starRingEnd ℂ) (heckeRecursionSeq (N : ℂ) lam om m) =
        heckeRecursionSeq (N : ℂ) ((starRingEnd ℂ) lam) ((starRingEnd ℂ) om) m ∧
      (starRingEnd ℂ) (heckeRecursionSeq (N : ℂ) lam om (m + 1)) =
        heckeRecursionSeq (N : ℂ) ((starRingEnd ℂ) lam) ((starRingEnd ℂ) om) (m + 1) from H.1
  induction m with
  | zero =>
    constructor
    · simp [heckeRecursionSeq]
    · simp [heckeRecursionSeq, map_div₀]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    show (starRingEnd ℂ) (heckeRecursionSeq (N : ℂ) lam om (m + 2)) =
        heckeRecursionSeq (N : ℂ) ((starRingEnd ℂ) lam) ((starRingEnd ℂ) om) (m + 2)
    simp only [heckeRecursionSeq, map_div₀, map_sub, map_mul, Complex.conj_natCast, ih.1, ih.2]

theorem torusFactor_natCast (N lam om : ℂ) (m : ℕ) :
    torusFactor N lam om (m : ℤ) = heckeRecursionSeq N lam om m := by
  simp [torusFactor]

theorem torusFactor_neg (N lam om : ℂ) {m : ℤ} (hm : m < 0) : torusFactor N lam om m = 0 := by
  simp [torusFactor, not_le.mpr hm]

section Matrices

variable {F : Type*} [Field F]

theorem diagZ_add (π : F) (hπ : π ≠ 0) (a b : ℤ) :
    diagZ π hπ (a + b) = diagZ π hπ a * diagZ π hπ b := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, Matrix.mul_apply, Fin.sum_univ_two, zpow_add₀ hπ]

theorem diagZ_zero' (π : F) (hπ : π ≠ 0) : diagZ π hπ 0 = 1 := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [diagZ]

theorem diagZ_one_pow (π : F) (hπ : π ≠ 0) (m : ℕ) : diagZ π hπ 1 ^ m = diagZ π hπ (m : ℤ) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, diagZ_zero']
  | succ m ih => rw [pow_succ, ih, ← diagZ_add]; push_cast; rfl

theorem diagZ_one_inv (π : F) (hπ : π ≠ 0) : (diagZ π hπ 1)⁻¹ = diagZ π hπ (-1) := by
  rw [inv_eq_iff_mul_eq_one, ← diagZ_add, show (1 : ℤ) + -1 = 0 by norm_num, diagZ_zero']

theorem diagZ_one_inv_pow (π : F) (hπ : π ≠ 0) (m : ℕ) :
    (diagZ π hπ 1)⁻¹ ^ m = diagZ π hπ (-(m : ℤ)) := by
  rw [diagZ_one_inv]
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, neg_zero, diagZ_zero']
  | succ m ih =>
    rw [pow_succ, ih, ← diagZ_add]
    congr 1
    push_cast
    ring

def scalarHom : Fˣ →* GL (Fin 2) F := Units.map (Matrix.scalar (Fin 2) : F →+* _).toMonoidHom

theorem scalarHom_coe_apply (t : Fˣ) (i j : Fin 2) :
    ((scalarHom t : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = if i = j then (t : F) else 0 := by
  show (Matrix.scalar (Fin 2) (t : F)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem scalarPi_eq_scalarHom (π : F) (hπ : π ≠ 0) : scalarPi π hπ = scalarHom (Units.mk0 π hπ) := by
  refine GeneralLinearGroup.ext fun i j => ?_
  rw [scalarHom_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [scalarPi]

theorem scalarHom_commute (t : Fˣ) (g : GL (Fin 2) F) : scalarHom t * g = g * scalarHom t := by
  refine Units.ext ?_
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (t : F) (fun r' => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) F)).eq

theorem unipotent_coe_apply (x : F) (i j : Fin 2) :
    ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = !![1, x; 0, 1] i j := rfl

theorem diagZ_coe_apply (π : F) (hπ : π ≠ 0) (m : ℤ) (i j : Fin 2) :
    ((diagZ π hπ m : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = !![π ^ m, 0; 0, 1] i j := rfl

end Matrices

end UnramW17

namespace UnramW17

section Local

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem exists_map_eq_of_integral (g : GL (Fin 2) (v.adicCompletion K))
    (hint : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K)
    (hdet : Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1) :
    ∃ k : GL (Fin 2) (v.adicCompletionIntegers K),
      Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k = g := by
  let M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) := Matrix.of fun i j => ⟨_, hint i j⟩
  have hM : (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).mapMatrix M =
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    ext i j; rfl
  have hdetM : (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) M.det =
      Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    rw [RingHom.map_det, hM]
  have hunit : IsUnit M.det := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    show Valued.v ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) M.det) = 1
    rw [hdetM, hdet]
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hunit, ?_⟩
  refine GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl

theorem exists_map_eq_unipotent (r : v.adicCompletionIntegers K) :
    ∃ k : GL (Fin 2) (v.adicCompletionIntegers K),
      Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k =
        unipotent (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) := by
  refine exists_map_eq_of_integral K v _ (fun i j => ?_) ?_
  · rw [unipotent_coe_apply]
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact r.2
    · exact zero_mem _
    · exact one_mem _
  · have : Matrix.det ((unipotent (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = 1 := by
      show Matrix.det !![(1 : v.adicCompletion K), _; 0, 1] = 1
      rw [Matrix.det_fin_two_of]; ring
    rw [this, map_one]

def swapGL : GL (Fin 2) (v.adicCompletion K) :=
  GeneralLinearGroup.mkOfDetNeZero !![(0 : v.adicCompletion K), 1; 1, 0]
    (by rw [Matrix.det_fin_two_of]; simp)

theorem swapGL_coe_apply (i j : Fin 2) :
    ((swapGL K v : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      !![(0 : v.adicCompletion K), 1; 1, 0] i j := rfl

theorem exists_map_eq_swapGL :
    ∃ k : GL (Fin 2) (v.adicCompletionIntegers K),
      Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k =
        swapGL K v := by
  refine exists_map_eq_of_integral K v _ (fun i j => ?_) ?_
  · rw [swapGL_coe_apply]
    fin_cases i <;> fin_cases j
    · exact zero_mem _
    · exact one_mem _
    · exact one_mem _
    · exact zero_mem _
  · show Valued.v (Matrix.det !![(0 : v.adicCompletion K), 1; 1, 0]) = 1
    rw [Matrix.det_fin_two_of]
    simp

theorem local_iwasawa_of_le (π : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π ≠ 0)
    (hπv : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) =
      WithZero.exp (-1 : ℤ))
    (g : GL (Fin 2) (v.adicCompletion K))
    (hg : Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      (max (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0))
        (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1))) ^ 2)
    (hle : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0) ≤
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1)) :
    ∃ (x : v.adicCompletion K) (j : ℤ) (k : GL (Fin 2) (v.adicCompletionIntegers K)),
      g = unipotent x * scalarHom (Units.mk0 _ hπ ^ j) *
        Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k := by
  set a := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 with hc
  set d := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 with hd
  rw [max_eq_right hle] at hg
  have hdetg : Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a * d - b * c :=
    Matrix.det_fin_two _
  have hdet0 : Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero
  have hd0 : d ≠ 0 := by
    intro h0
    have h : Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 0 := by
      rw [hg, h0, map_zero, zero_pow two_ne_zero]
    exact hdet0 ((Valuation.zero_iff Valued.v).mp h)
  have hvd0 : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0
  set n : ℤ := WithZero.log (Valued.v d) with hn
  have hvd : Valued.v d = WithZero.exp n := (WithZero.exp_log hvd0).symm
  set s : v.adicCompletion K := (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^ (-n) with hs
  have hvs : Valued.v s = WithZero.exp n := by
    rw [hs, map_zpow₀, hπv, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]
  have hs0 : s ≠ 0 := by rw [hs]; exact zpow_ne_zero _ hπ
  have hvs0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs0

  set α : v.adicCompletion K := (a - b / d * c) / s with hα
  have hαds : α * d * s = Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    rw [hdetg, hα]; field_simp
  have hvα : Valued.v α = 1 := by
    have h := congrArg Valued.v hαds
    rw [map_mul, map_mul, hg, hvd, hvs, sq] at h
    have hn0 : WithZero.exp n ≠ 0 := WithZero.exp_ne_zero
    calc Valued.v α = Valued.v α * WithZero.exp n * WithZero.exp n / (WithZero.exp n * WithZero.exp n) := by
          field_simp
      _ = 1 := by rw [h]; field_simp
  have hα0 : α ≠ 0 := fun h => by rw [h, map_zero] at hvα; exact zero_ne_one hvα
  have hkdet : Matrix.det !![α, 0; c / s, d / s] ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simp only [zero_mul, sub_zero]
    exact mul_ne_zero hα0 (div_ne_zero hd0 hs0)
  set kF : GL (Fin 2) (v.adicCompletion K) := GeneralLinearGroup.mkOfDetNeZero _ hkdet with hkF
  have hkFij : ∀ i j, (kF : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j = !![α, 0; c / s, d / s] i j :=
    fun i j => rfl
  have hint : ∀ i j, (kF : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
    intro i j
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hkFij]
    fin_cases i <;> fin_cases j
    · show Valued.v α ≤ 1
      rw [hvα]
    · show Valued.v (0 : v.adicCompletion K) ≤ 1
      rw [map_zero]; exact zero_le'
    · show Valued.v (c / s) ≤ 1
      rw [map_div₀, hvs, ← hvd]
      exact div_le_one_of_le₀ hle zero_le'
    · show Valued.v (d / s) ≤ 1
      rw [map_div₀, hvs, hvd, div_self WithZero.exp_ne_zero]
  have hkdet1 : Valued.v (Matrix.det (kF : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
    show Valued.v (Matrix.det !![α, 0; c / s, d / s]) = 1
    rw [Matrix.det_fin_two_of]
    simp only [zero_mul, sub_zero]
    rw [map_mul, hvα, map_div₀, hvs, hvd, div_self WithZero.exp_ne_zero, one_mul]
  obtain ⟨k, hk⟩ := exists_map_eq_of_integral K v kF hint hkdet1
  refine ⟨b / d, -n, k, ?_⟩
  rw [hk]
  have hS : ∀ i j, ((scalarHom (Units.mk0 _ hπ ^ (-n)) : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j = if i = j then s else 0 := by
    intro i j
    rw [scalarHom_coe_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  refine GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [unipotent_coe_apply, hS, hkFij, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  fin_cases i <;> fin_cases j
  · show a = _
    simp
    rw [hα]; field_simp; ring
  · show b = _
    simp; field_simp
  · show c = _
    simp; field_simp
  · show d = _
    simp; field_simp

end Local

end UnramW17

namespace UnramW17

section Local2

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem local_iwasawa (π : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π ≠ 0)
    (hπv : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) =
      WithZero.exp (-1 : ℤ))
    (g : GL (Fin 2) (v.adicCompletion K))
    (hg : Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      (max (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0))
        (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1))) ^ 2) :
    ∃ (x : v.adicCompletion K) (j : ℤ) (k : GL (Fin 2) (v.adicCompletionIntegers K)),
      g = unipotent x * scalarHom (Units.mk0 _ hπ ^ j) *
        Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k := by
  rcases le_or_gt (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0))
      (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1)) with hle | hlt
  · exact local_iwasawa_of_le K v π hπ hπv g hg hle
  · obtain ⟨w, hw⟩ := exists_map_eq_swapGL K v
    have h10 : ((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, swapGL_coe_apply, swapGL_coe_apply]
      simp
    have h11 : ((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, swapGL_coe_apply, swapGL_coe_apply]
      simp
    have hdet : Matrix.det ((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = -Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      rw [Units.val_mul, Matrix.det_mul]
      show _ * Matrix.det !![(0 : v.adicCompletion K), 1; 1, 0] = _
      rw [Matrix.det_fin_two_of]; ring
    have hg₂ : Valued.v (Matrix.det ((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
        (max (Valued.v (((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0))
          (Valued.v (((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1))) ^ 2 := by
      rw [hdet, Valuation.map_neg, h10, h11, max_comm]; exact hg
    obtain ⟨x, j, k, hk⟩ := local_iwasawa_of_le K v π hπ hπv _ hg₂ (by rw [h10, h11]; exact hlt.le)
    refine ⟨x, j, k * w⁻¹, ?_⟩
    rw [map_mul, map_inv, hw, ← mul_assoc, ← hk, mul_inv_cancel_right]

end Local2

theorem norm_addChar_apply_eq_one (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (y : v.adicCompletion K) : ‖ψ y‖ = 1 := by
  obtain ⟨b, hb0, hb⟩ :=
    HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (K := K) v y
  set N : ℕ := Ideal.absNorm (Ideal.span {b}) with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero hb0
  have hNmem : (N : 𝓞 K) ∈ Ideal.span {b} := Ideal.absNorm_mem _
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hNmem
  have hmem : (N : v.adicCompletion K) * y ∈ v.adicCompletionIntegers K := by
    have e : (N : v.adicCompletion K) =
        algebraMap (𝓞 K) (v.adicCompletion K) b * algebraMap (𝓞 K) (v.adicCompletion K) r := by
      rw [← map_mul, mul_comm, hr, map_natCast]
    rw [e, mul_comm, ← mul_assoc]
    exact mul_mem hb (HeightOneSpectrum.coe_mem_adicCompletionIntegers v r)
  have h1 : ψ y ^ N = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    exact hψ0 ⟨_, hmem⟩
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).mp h2

theorem addChar_mul_conj_eq_one (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (y : v.adicCompletion K) : ψ y * (starRingEnd ℂ) (ψ y) = 1 := by
  rw [Complex.mul_conj', norm_addChar_apply_eq_one K v ψ hψ0 y]
  simp

section Adelic

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

def cpt : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (v.adicCompletion K) :=
  (finComponent R K v).comp (glFin R K)

theorem coe_cpt (h : GL (Fin 2) (AdeleRing R K)) :
    ((cpt K v h : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      (finAdeleEval R K v).mapMatrix ((adeleFin R K).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing R K))) :=
  rfl

theorem cpt_apply (h : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    ((cpt K v h : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 v :=
  rfl

theorem coe_placeEmbed (X : GL (Fin 2) (v.adicCompletion K)) :
    ((placeEmbed K v X : GL (Fin 2) (AdeleRing R K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) =
      finMat R K (localMat R K v (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) :=
  rfl

theorem cpt_placeEmbed (X : GL (Fin 2) (v.adicCompletion K)) : cpt K v (placeEmbed K v X) = X := by
  show finComponent R K v (glFin R K (finEmbed R K (localEmbed R K v X))) = X
  rw [glFin_finEmbed, finComponent_localEmbed_self]

theorem det_cpt (g : GL (Fin 2) (AdeleRing R K)) :
    Matrix.det ((cpt K v g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      (((Matrix.GeneralLinearGroup.det g : (AdeleRing R K)ˣ) : AdeleRing R K)).2 v := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_cpt, ← RingHom.map_det, ← RingHom.map_det]
  rfl

theorem placeEmbed_mul_eq_mul_of_commute (X : GL (Fin 2) (v.adicCompletion K)) (h : GL (Fin 2) (AdeleRing R K))
    (hc : (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
        ((cpt K v h : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ((cpt K v h : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * X) :
    placeEmbed K v X * h = h * placeEmbed K v X := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_placeEmbed]
  refine matrix_eq_of_mapMatrix_arch_fin_eq R K ?_ ?_
  · rw [map_mul, map_mul, mapMatrix_arch_finMat, one_mul, mul_one]
  · rw [map_mul, map_mul, mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw; rw [mapMatrix_localMat_self]; exact hc
    · rw [mapMatrix_localMat_of_ne R K v _ hw, one_mul, mul_one]

theorem mul_placeEmbed_comm_of_cpt_eq_one (h : GL (Fin 2) (AdeleRing R K)) (h1 : cpt K v h = 1)
    (X : GL (Fin 2) (v.adicCompletion K)) : h * placeEmbed K v X = placeEmbed K v X * h := by
  refine (placeEmbed_mul_eq_mul_of_commute K v X h ?_).symm
  rw [h1, Units.val_one, mul_one, one_mul]

theorem placeEmbed_scalarHom_mul_comm (t : (v.adicCompletion K)ˣ) (h : GL (Fin 2) (AdeleRing R K)) :
    placeEmbed K v (scalarHom t) * h = h * placeEmbed K v (scalarHom t) :=
  placeEmbed_mul_eq_mul_of_commute K v _ h
    (Matrix.scalar_commute (t : v.adicCompletion K) (fun _ => Commute.all _ _) _).eq

theorem cpt_inv_placeEmbed_cpt_mul (g : GL (Fin 2) (AdeleRing R K)) :
    cpt K v ((placeEmbed K v (cpt K v g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, cpt_placeEmbed, inv_mul_cancel]

theorem valued_eq_of_placeEmbed_diagZ_eq_heckeGen (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hgen : placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) =
      heckeGen R K v) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) := by
  have h := congrArg (fun y => ((cpt K v y : GL (Fin 2) (v.adicCompletion K)) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0) hgen
  rw [cpt_placeEmbed, diagZ_coe_apply, cpt_apply, heckeGen, heckeGenAt_snd_apply_self] at h
  simp at h
  rw [show (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ : v.adicCompletion K) =
    (uniformizerUnit K v : v.adicCompletion K) from h]
  exact valued_uniformizerUnit K v

end Adelic

end UnramW17

namespace UnramW17

theorem torusFactor_zero (N lam om : ℂ) : torusFactor N lam om 0 = 1 := by
  simp [torusFactor, heckeRecursionSeq]

theorem diagZ_mul_unipotent' {F : Type*} [Field F] (π : F) (hπ : π ≠ 0) (m : ℤ) (x : F) :
    diagZ π hπ m * unipotent x = unipotent (π ^ m * x) * diagZ π hπ m := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, unipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_scalarHom_comm {F : Type*} [Field F] (x : F) (t : Fˣ) :
    scalarHom t * unipotent x = unipotent x * scalarHom t :=
  scalarHom_commute t _

section Key

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem exists_central_value (W : GL (Fin 2) (AdeleRing R K) → ℂ) (ϖ : v.adicCompletion K) (hπ : ϖ ≠ 0)
    (om : ℂ) (hZ : ∀ g : GL (Fin 2) (AdeleRing R K), W (g * placeEmbed K v (scalarPi ϖ hπ)) = om * W g)
    (j : ℤ) :
    ∃ c : ℂ, ∀ h : GL (Fin 2) (AdeleRing R K),
      W (h * placeEmbed K v (scalarHom (Units.mk0 ϖ hπ ^ j))) = c * W h := by
  have hP : placeEmbed K v (scalarHom (Units.mk0 ϖ hπ ^ j)) = (placeEmbed K v (scalarPi ϖ hπ)) ^ j := by
    rw [map_zpow, ← scalarPi_eq_scalarHom, map_zpow]
  rw [hP]
  set P := placeEmbed K v (scalarPi ϖ hπ) with hPdef
  have hnat : ∀ (n : ℕ) (h : GL (Fin 2) (AdeleRing R K)), W (h * P ^ n) = om ^ n * W h := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih => intro h; rw [pow_succ, ← mul_assoc, hZ, ih, pow_succ]; ring
  by_cases hom : om = 0
  · refine ⟨0, fun h => ?_⟩
    have hW : ∀ g : GL (Fin 2) (AdeleRing R K), W g = 0 := fun g => by
      have e := hZ (g * P⁻¹)
      rw [inv_mul_cancel_right, hom, zero_mul] at e
      exact e
    rw [hW, hW, mul_zero]
  · refine ⟨om ^ j, fun h => ?_⟩
    rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
    · rw [zpow_natCast, zpow_natCast, hnat]
    · have e := hnat n (h * P ^ (-(n : ℤ)))
      rw [mul_assoc, ← zpow_natCast, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one] at e
      rw [_root_.zpow_neg om, zpow_natCast, e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hom), one_mul]

theorem key_identity (W : GL (Fin 2) (AdeleRing R K) → ℂ) (ψ : AddChar (v.adicCompletion K) ℂ)
    (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) (lam om : ℂ)
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers K)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing R K)),
      W (placeEmbed K v (unipotent x) * g) = ψ x * W g)
    (hK : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing R K)),
      W (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing R K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing R K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om * W g)
    (x : v.adicCompletion K) (j : ℤ) (k : GL (Fin 2) (v.adicCompletionIntegers K))
    (g' : GL (Fin 2) (AdeleRing R K)) (hg' : cpt K v g' = 1) :
    ∃ c : ℂ, ∀ m : ℤ,
      W (placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ m) *
          (placeEmbed K v (unipotent x * scalarHom (Units.mk0 _ hπ ^ j) *
            Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k) * g')) =
        ψ ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ^ m * x) * c *
          (W g' * torusFactor (Fintype.card I) lam om m) := by
  obtain ⟨c, hc⟩ := exists_central_value K v W _ hπ om hZ j
  refine ⟨c, fun m => ?_⟩
  set ϖF := algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ with hϖF
  have hK' : ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing R K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g := by
    intro r g
    obtain ⟨kr, hkr⟩ := exists_map_eq_unipotent K v r
    rw [← hkr]
    exact hK kr g
  have hg'c : ∀ X : GL (Fin 2) (v.adicCompletion K), g' * placeEmbed K v X = placeEmbed K v X * g' :=
    mul_placeEmbed_comm_of_cpt_eq_one K v g' hg'

  have e1 : placeEmbed K v (diagZ ϖF hπ m) *
        (placeEmbed K v (unipotent x * scalarHom (Units.mk0 ϖF hπ ^ j) *
          Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k) * g') =
      placeEmbed K v (unipotent (ϖF ^ m * x)) *
        ((placeEmbed K v (diagZ ϖF hπ m) * g') * placeEmbed K v (scalarHom (Units.mk0 ϖF hπ ^ j)) *
          placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k)) := by
    rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, diagZ_mul_unipotent', map_mul]
    simp only [mul_assoc]
    congr 2
    symm
    rw [← mul_assoc, hg'c, mul_assoc, hg'c]
  rw [e1, hN, hK, hc, ← hg'c,
    UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor v hπ b hψ0 hψ1 hN hK' hT hZ hg'c m]
  ring

end Key

end UnramW17

end

open UnramW17

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψv : AddChar (v.adicCompletion K) ℂ) (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hgen : placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) =
      heckeGen (𝓞 K) K v)
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers K)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers K,
      ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1)
    (W W' : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (lam om lam' om' : ℂ)
    (hN : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent x) * g) = ψv x * W g)
    (hN' : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W' (placeEmbed K v (unipotent x) * g) = ψv x * W' g)
    (hK : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W g)
    (hK' : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W' (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W' g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam * W g)
    (hT' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W' (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W' (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam' * W' g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om * W g)
    (hZ' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W' (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om' * W' g)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hg : Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2) :
    (∀ m : ℕ,
      W ((heckeGen (𝓞 K) K v) ^ m * g) * (starRingEnd ℂ) (W' ((heckeGen (𝓞 K) K v) ^ m * g)) =
        heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam om m *
          heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ((starRingEnd ℂ) lam') ((starRingEnd ℂ) om') m *
          (W g * (starRingEnd ℂ) (W' g))) ∧
    (∀ m : ℕ, 0 < m → W ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0) := by
  have hπv : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) :=
    valued_eq_of_placeEmbed_diagZ_eq_heckeGen K v ϖ hπ hgen

  set X : GL (Fin 2) (v.adicCompletion K) := cpt K v g with hX
  set g' : GL (Fin 2) (AdeleRing (𝓞 K) K) := (placeEmbed K v X)⁻¹ * g with hg'def
  have hg' : cpt K v g' = 1 := cpt_inv_placeEmbed_cpt_mul K v g
  have hgX : g = placeEmbed K v X * g' := by rw [hg'def, mul_inv_cancel_left]

  have hXshell : Valued.v (Matrix.det (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      (max (Valued.v ((X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0))
        (Valued.v ((X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1))) ^ 2 := by
    rw [hX, det_cpt, cpt_apply, cpt_apply]; exact hg
  obtain ⟨x, j, k, hXeq⟩ := local_iwasawa K v ϖ hπ hπv X hXshell

  obtain ⟨c, hc⟩ := key_identity K v W ψv ϖ hπ lam om b hψ0 hψ1 hN hK hT hZ x j k g' hg'
  obtain ⟨c', hc'⟩ := key_identity K v W' ψv ϖ hπ lam' om' b hψ0 hψ1 hN' hK' hT' hZ' x j k g' hg'
  have hψu : ∀ y : v.adicCompletion K, ψv y * (starRingEnd ℂ) (ψv y) = 1 :=
    addChar_mul_conj_eq_one K v ψv hψ0

  have hGm : ∀ m : ℕ, (heckeGen (𝓞 K) K v) ^ m = placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ (m : ℤ)) := fun m => by
    rw [← hgen, ← map_pow, diagZ_one_pow]
  have hGinv : ∀ m : ℕ, (heckeGen (𝓞 K) K v)⁻¹ ^ m = placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ (-(m : ℤ))) := fun m => by
    rw [← hgen, ← map_inv, ← map_pow, diagZ_one_inv_pow]
  have hW0 : W g = ψv x * c * W g' := by
    have e := hc 0
    rw [diagZ_zero', map_one, one_mul, zpow_zero, one_mul, ← hXeq, ← hgX, torusFactor_zero, mul_one] at e
    exact e
  have hW0' : W' g = ψv x * c' * W' g' := by
    have e := hc' 0
    rw [diagZ_zero', map_one, one_mul, zpow_zero, one_mul, ← hXeq, ← hgX, torusFactor_zero, mul_one] at e
    exact e
  have hcard : (Fintype.card I : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by rw [hI]
  refine ⟨fun m => ?_, fun m hm => ?_⟩
  · have e := hc m
    have e' := hc' m
    rw [← hXeq, ← hgX, ← hGm, torusFactor_natCast, hcard] at e e'
    rw [e, e', hW0, hW0']
    simp only [map_mul, conj_heckeRecursionSeq]
    have u1 := hψu ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ^ (m : ℤ) * x)
    have u0 := hψu x
    linear_combination
      (c * (starRingEnd ℂ) c' * (W g' * (starRingEnd ℂ) (W' g')) *
        (heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam om m *
          heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ((starRingEnd ℂ) lam') ((starRingEnd ℂ) om') m)) *
        (u1 - u0)
  · have e := hc (-(m : ℤ))
    rw [← hXeq, ← hgX, ← hGinv, torusFactor_neg _ _ _ (by omega)] at e
    rw [e, mul_zero, mul_zero]

end S_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero
end P2MW
export P2MW.S_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero (solution)
