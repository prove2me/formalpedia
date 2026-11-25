-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.keyExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:54:19.435928+00:00
-- url     : https://prove2.me/submissions/d3b121b3-248b-4315-8016-58838a9b06f1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
private theorem sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (i₀ : m) (φ : ℂ)
    (g : m → ℂ) :
    stdH L m (Pi.single i₀ φ) g = ((area L : ℂ))⁻¹ * (φ * conj (g i₀)) ∧
    stdH L m g (Pi.single i₀ φ) = ((area L : ℂ))⁻¹ * (g i₀ * conj φ) := by
  constructor
  · simp [stdH, matH, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply]
    ring
  · simp [stdH, matH, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply,
      apply_ite (starRingEnd ℂ), mul_ite]
    ring
private theorem H_affine_combination_eq_of_quadratic_relation {m : Type} [Fintype m] [DecidableEq m] (H : PI.ULS.Sesq (m → ℂ))
    (f w : m → ℂ) (κ rc Q N₁ γ ε : ℂ) (hN : N₁ ≠ 0)
    (hff : H f f = κ * Q) (hww : H w w = κ * Q * (1 + ε)) (hX : N₁ * (H f w + H w f) = κ * γ)
    (hrc : conj rc = rc) (hrD : rc * (N₁ * (2 * Q + Q * ε) - γ) = N₁ * Q * ε) :
    H (w + rc • (f - w)) (w + rc • (f - w)) = κ * Q := by
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hrc]
  apply mul_left_cancel₀ hN
  linear_combination (N₁ * (1 - 2 * rc + rc ^ 2)) * hww + (N₁ * rc ^ 2) * hff +
    (rc - rc ^ 2) * hX + (κ * (rc - 1)) * hrD
private theorem cmTheta_add_conj_and_mul_conj (a : ℕ) (b c : ℤ) (d : ℕ) (h : CmOK a b c d) :
    cmTheta b d + conj (cmTheta b d) = b ∧ cmTheta b d * conj (cmTheta b d) = (a:ℂ) * c := by
  obtain ⟨h4, -, -, -⟩ := h
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have h4' : (4:ℂ) * a * c = (b:ℂ)^2 + d := by exact_mod_cast h4
  have hc : conj (cmTheta b d) = ((b:ℂ) - Complex.I * (Real.sqrt d : ℝ)) / 2 := by
    simp [cmTheta, map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hc]
  constructor
  · simp only [cmTheta]; ring
  · simp only [cmTheta]
    linear_combination (-((Real.sqrt d : ℝ) : ℂ)^2/4) * Complex.I_sq + (1/4) * hs - (1/4) * h4'
private theorem not_pow_dvd_two_mul_mul_of_not_dvd (l : ℕ) (hl : Nat.Prime l) (g k : ℕ) (hk : 3 ≤ k) (M₄ n₁ : ℕ)
    (hM : ¬ l ∣ M₄) (hn : ¬ l ∣ n₁) (Q₀ p q : ℤ) (hQ : ¬ (l:ℤ) ∣ Q₀) (hq : ¬ (l:ℤ) ∣ q) :
    ¬ (l:ℤ) ^ (g + 3) ∣ 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) := by
  intro hdvd
  have hp : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
  have hne : (l:ℤ) ^ g ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have h1 : (l:ℤ) ^ 3 ∣ ((M₄:ℤ) * n₁ * Q₀) * (2 * (2 * q + (l:ℤ) ^ k * p)) := by
    have e1 : (l:ℤ) ^ (g + 3) = (l:ℤ) ^ g * (l:ℤ) ^ 3 := pow_add _ _ _
    have e2 : 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) =
        (l:ℤ) ^ g * (((M₄:ℤ) * n₁ * Q₀) * (2 * (2 * q + (l:ℤ) ^ k * p))) := by
      push_cast; ring
    rw [e1, e2] at hdvd
    exact (mul_dvd_mul_iff_left hne).mp hdvd
  have hnd : ¬ (l:ℤ) ∣ ((M₄:ℤ) * n₁ * Q₀) := by
    intro h
    rcases hp.dvd_or_dvd h with h | h
    · rcases hp.dvd_or_dvd h with h | h
      · exact hM (Int.natCast_dvd_natCast.mp h)
      · exact hn (Int.natCast_dvd_natCast.mp h)
    · exact hQ h
  have h2 := hp.pow_dvd_of_dvd_mul_left 3 hnd h1
  have h3 : (l:ℤ) ^ 3 ∣ 2 * (l:ℤ) ^ k * p :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ hk) _) _
  have h4 : (l:ℤ) ^ 3 ∣ q * 4 := by
    have e3 : q * 4 = 2 * (2 * q + (l:ℤ) ^ k * p) - 2 * (l:ℤ) ^ k * p := by ring
    rw [e3]
    exact dvd_sub h2 h3
  have h5 := hp.pow_dvd_of_dvd_mul_left 3 hq h4
  have h6 := Int.le_of_dvd (by norm_num) h5
  have hl2 : (2:ℤ) ≤ l := by exact_mod_cast hl.two_le
  have h7 : (2:ℤ) ^ 3 ≤ (l:ℤ) ^ 3 := by gcongr
  linarith
private theorem natAbs_smul_mem_of_zsmul_mem {V : Type} [AddCommGroup V] (Λ : AddSubgroup V) (z : ℤ) (v : V)
    (h : z • v ∈ Λ) : z.natAbs • v ∈ Λ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · simpa [natCast_zsmul] using h
  · simpa [natCast_zsmul] using h
private theorem zsmul_affine_combination_eq {m : Type} (w f : m → ℂ) (E₀ P : ℤ) (n₁ M₃ l t h : ℕ) (hE : (E₀:ℂ) ≠ 0) :
    (E₀ * n₁ * M₃ : ℤ) • (w + ((l:ℂ) ^ (t + h) * P / E₀) • (f - w)) =
      (M₃ * E₀ - (l:ℤ) ^ (t + h) * P * M₃) • (n₁ • w) + ((l:ℤ) ^ t * P * n₁) • ((l ^ h * M₃) • f) := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
  simp only [zsmul_eq_mul, nsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution : KeyExact := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ hK
  obtain ⟨hcm, -, -, hr1, hr2, hl, hQ, hi₀, -⟩ := hK
  have hl1 : l ≠ 1 := hl.one_lt.ne'
  obtain ⟨g, M₄, hM₄, hM₁⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr1 l hl1
  obtain ⟨h, M₃, hM₃, hM₂⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr2 l hl1
  refine ⟨g + h + 3, fun k hk w hw => ?_⟩
  obtain ⟨⟨n₁, hn₁, hn₁w⟩, hzero, p, q, hlq, hHw⟩ := hw
  obtain ⟨hθs, hθp⟩ := cmTheta_add_conj_and_mul_conj a b c d hcm
  set L := cmL a b d ha hd lam hlam with hLdef
  set θ := cmTheta b d with hθdef
  set φ : ℂ := lam * (↑x * ↑a + ↑y * θ) with hφ
  have hf : fvec a b d lam x y i₀ = Pi.single i₀ φ := rfl
  rw [hf] at hHw ⊢
  have hω1 : L.ω₁ = lam * a := rfl
  have hω2 : L.ω₂ = lam * θ := rfl
  have hwstd : (relIdx (stdLat L m) Λ) • (n₁ • w) ∈ stdLat L m :=
    AddSubgroup.nsmul_relIndex_mem (stdLat L m) hn₁w
  rw [hM₁] at hwstd
  have hw0 := (AddSubgroup.mem_pi _).mp hwstd i₀ (Set.mem_univ _)
  obtain ⟨α, β, hαβ⟩ := PeriodPair.mem_lattice.mp hw0
  set N₁ : ℕ := l ^ g * M₄ * n₁ with hN₁
  have hwi : (N₁:ℂ) * w i₀ = lam * (α * a + β * θ) := by
    have e : ((l ^ g * M₄) • n₁ • w) i₀ = (N₁:ℂ) * w i₀ := by
      simp [hN₁, nsmul_eq_mul]
      ring
    rw [← e, ← hαβ, hω1, hω2]
    ring
  have hfΛ : (relIdx Λ (stdLat L m)) • (Pi.single i₀ φ) ∈ Λ := by
    apply AddSubgroup.nsmul_relIndex_mem Λ
    rw [stdLat, AddSubgroup.mem_pi]
    intro i _
    by_cases hi : i = i₀
    · subst hi
      simp only [Pi.single_eq_same]
      exact PeriodPair.mem_lattice.mpr ⟨x, y, by rw [hω1, hω2, hφ]; ring⟩
    · simp [Pi.single_eq_of_ne hi]
  rw [hM₂] at hfΛ
  set A : ℂ := ((area L : ℂ))⁻¹ with hA
  set Q₀ : ℤ := ↑a * x ^ 2 + b * x * y + c * y ^ 2 with hQ₀
  set γ : ℤ := 2 * α * x * a + (α * y + β * x) * b + 2 * β * y * c with hγ
  set κ : ℂ := A * (lam * conj lam * a) with hκ
  have hcφ : conj φ = conj lam * (x * a + y * conj θ) := by simp [hφ]
  have hff : stdH L m (Pi.single i₀ φ) (Pi.single i₀ φ) = κ * Q₀ := by
    rw [(sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ _).1]
    simp only [Pi.single_eq_same]
    rw [hcφ, hφ, hκ, hQ₀]
    push_cast
    linear_combination (A * lam * conj lam * x * y * a) * hθs + (A * lam * conj lam * y ^ 2) * hθp
  have hwc : (N₁:ℂ) * conj (w i₀) = conj lam * (α * a + β * conj θ) := by
    have := congrArg (starRingEnd ℂ) hwi
    simpa using this
  have hX : (N₁:ℂ) * (stdH L m (Pi.single i₀ φ) w + stdH L m w (Pi.single i₀ φ)) = κ * γ := by
    rw [(sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ w).1, (sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ w).2, hcφ, hφ, hκ, hγ]
    push_cast
    linear_combination (A * lam * (x * a + y * θ)) * hwc +
      (A * conj lam * (x * a + y * conj θ)) * hwi +
      (A * lam * conj lam * a * (x * β + y * α)) * hθs + (A * lam * conj lam * 2 * β * y) * hθp
  have hww : stdH L m w w = κ * Q₀ * (1 + (l:ℂ) ^ k * p / q) := by rw [hHw, hff]
  have hsum := not_pow_dvd_two_mul_mul_of_not_dvd l hl g k (by omega) M₄ n₁ hM₄ hn₁ Q₀ p q hQ hlq
  obtain ⟨w', γ', hw'Λ, hw'z, hw'w, hw'X, hndv⟩ : ∃ (w' : m → ℂ) (γ' : ℤ), n₁ • w' ∈ Λ ∧
      (∀ j ∈ T, w' j = 0) ∧ stdH L m w' w' = κ * Q₀ * (1 + (l:ℂ) ^ k * p / q) ∧
      (N₁:ℂ) * (stdH L m (Pi.single i₀ φ) w' + stdH L m w' (Pi.single i₀ φ)) = κ * γ' ∧
      ¬ (l:ℤ) ^ (g + 3) ∣ (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ' * q := by
    by_cases hE : (l:ℤ) ^ (g + 3) ∣ (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ * q
    · refine ⟨-w, -γ, ?_, ?_, ?_, ?_, ?_⟩
      · rw [smul_neg]; exact neg_mem hn₁w
      · intro j hj; simp [hzero j hj]
      · simp [hww]
      · simp only [map_neg, LinearMap.neg_apply]
        push_cast
        linear_combination -hX
      · intro hE'
        apply hsum
        have e : 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) =
            ((N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ * q) +
            ((N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - (-γ) * q) := by
          rw [hN₁]
          push_cast
          ring
        rw [e]
        exact dvd_add hE hE'
    · exact ⟨w, γ, hn₁w, hzero, hww, hX, hE⟩
  set E : ℤ := (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ' * q with hEdef
  have hE0 : E ≠ 0 := fun h0 => hndv (h0 ▸ dvd_zero _)
  obtain ⟨j, e₀, he₀, hEabs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hE0) l hl1
  have hj : j ≤ g + 2 := by
    by_contra hj
    apply hndv
    have h1 : l ^ (g + 3) ∣ E.natAbs := hEabs ▸ Dvd.dvd.mul_right (pow_dvd_pow l (by omega)) _
    have h2 : ((l ^ (g + 3) : ℕ) : ℤ) ∣ E := Int.natCast_dvd.mpr h1
    simpa using h2
  set E₀ : ℤ := E.sign * e₀ with hE₀def
  have hEE : E = (l:ℤ) ^ j * E₀ := by
    conv_lhs => rw [← Int.sign_mul_natAbs E, hEabs]
    rw [hE₀def]
    push_cast
    ring
  have hE₀ : ¬ (l:ℤ) ∣ E₀ := by
    intro hd'
    apply he₀
    have h1 := Int.natCast_dvd.mp hd'
    rwa [hE₀def, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hE0, one_mul, Int.natAbs_natCast] at h1
  have hE₀ne : (E₀:ℂ) ≠ 0 := by
    have : E₀ ≠ 0 := fun h0 => hE₀ (h0 ▸ dvd_zero _)
    exact_mod_cast this
  have hqne : (q:ℂ) ≠ 0 := by
    have : q ≠ 0 := fun h0 => hlq (h0 ▸ dvd_zero _)
    exact_mod_cast this
  have hN₁ne : (N₁:ℂ) ≠ 0 := by
    have hM₄0 : M₄ ≠ 0 := by rintro rfl; exact hM₄ (dvd_zero _)
    have hn₁0 : n₁ ≠ 0 := by rintro rfl; exact hn₁ (dvd_zero _)
    have : N₁ ≠ 0 := by
      rw [hN₁]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl.ne_zero) hM₄0) hn₁0
    exact_mod_cast this
  set t := k - j - h with ht
  have hkj : k - j = t + h := by omega
  set P : ℤ := Q₀ * p * N₁ with hP
  set rc : ℂ := (l:ℂ) ^ (k - j) * P / E₀ with hrcdef
  have hrc : conj rc = rc := by
    rw [hrcdef]
    simp [map_div₀]
  have hrD : rc * (N₁ * (2 * (Q₀:ℂ) + Q₀ * ((l:ℂ) ^ k * p / q)) - γ') =
      N₁ * Q₀ * ((l:ℂ) ^ k * p / q) := by
    have hEc : (E:ℂ) = (l:ℂ) ^ j * E₀ := by exact_mod_cast hEE
    have hEc2 : (E:ℂ) = N₁ * Q₀ * (2 * q + (l:ℂ) ^ k * p) - γ' * q := by
      rw [hEdef]; push_cast; ring
    have hpow : (l:ℂ) ^ k = (l:ℂ) ^ (k - j) * (l:ℂ) ^ j := by
      rw [← pow_add]; congr 1; omega
    have e1 : (N₁:ℂ) * (2 * (Q₀:ℂ) + Q₀ * ((l:ℂ) ^ k * p / q)) - γ' = (l:ℂ) ^ j * E₀ / q := by
      rw [← hEc, hEc2]
      field_simp
      try ring
    rw [e1, hrcdef, hP, hpow]
    push_cast
    field_simp
    try ring
  refine ⟨w' + rc • (Pi.single i₀ φ - w'), ?_, ?_, ?_⟩
  · have hmem : (E₀ * n₁ * M₃ : ℤ) • (w' + rc • (Pi.single i₀ φ - w')) ∈ Λ := by
      have key : (E₀ * n₁ * M₃ : ℤ) • (w' + rc • (Pi.single i₀ φ - w')) =
          (M₃ * E₀ - (l:ℤ) ^ (k - j) * P * M₃) • (n₁ • w') +
          ((l:ℤ) ^ t * P * n₁) • ((l ^ h * M₃) • Pi.single i₀ φ) := by
        rw [hrcdef, hkj]
        exact zsmul_affine_combination_eq w' (Pi.single i₀ φ) E₀ P n₁ M₃ l t h hE₀ne
      rw [key]
      exact add_mem (AddSubgroup.zsmul_mem _ hw'Λ _) (AddSubgroup.zsmul_mem _ hfΛ _)
    refine ⟨(E₀ * n₁ * M₃).natAbs, ?_, natAbs_smul_mem_of_zsmul_mem Λ _ _ hmem⟩
    intro hd'
    have hp : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
    have h1 : (l:ℤ) ∣ E₀ * n₁ * M₃ := Int.natCast_dvd.mpr hd'
    rcases hp.dvd_or_dvd h1 with h2 | h2
    · rcases hp.dvd_or_dvd h2 with h3 | h3
      · exact hE₀ h3
      · exact hn₁ (Int.natCast_dvd_natCast.mp h3)
    · exact hM₃ (Int.natCast_dvd_natCast.mp h2)
  · intro j' hj'
    have hne : j' ≠ i₀ := fun h' => hi₀ (h' ▸ hj')
    simp [hw'z j' hj', Pi.single_eq_of_ne hne]
  · rw [H_affine_combination_eq_of_quadratic_relation (stdH L m) (Pi.single i₀ φ) w' κ rc Q₀ N₁ γ' ((l:ℂ) ^ k * p / q) hN₁ne hff hw'w
      hw'X hrc hrD, hff]
end PI.UnitaryGroupMassFormula.UnimodLocStd
