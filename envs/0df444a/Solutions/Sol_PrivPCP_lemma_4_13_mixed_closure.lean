-- Prove2me | solution 1 for PrivPCP.lemma_4_13_mixed_closure
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:49:16.637386+00:00
-- url     : https://prove2.me/submissions/2d12f031-cf98-4787-baae-4754dfe9fff1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PrivPCP_Supplement_gammaF
import Theorems.Thm_PrivPCP_lemma_4_13_zero_count
import Theorems.Thm_PrivPCP_lemma_4_13_gamma_upper


namespace PrivPCP.FF

open MvPolynomial

variable {K : Type} [Field K]

/-- the function field of the curve `F = 0` -/
theorem exists_function_field (F : MvPolynomial (Fin 2) K) (hF : Irreducible F) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (x y : L),
      RingHom.ker (MvPolynomial.aeval (R := K) ![x, y]).toRingHom = Ideal.span {F} ∧
      IntermediateField.adjoin K {x, y} = ⊤ := by
  set I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {F}
  have hI : I.IsPrime := (Ideal.span_singleton_prime hF.ne_zero).2 hF.prime
  set Q := MvPolynomial (Fin 2) K ⧸ I
  haveI : IsDomain Q := Ideal.Quotient.isDomain I
  set L := FractionRing Q
  set x : L := algebraMap Q L (Ideal.Quotient.mk I (X 0))
  set y : L := algebraMap Q L (Ideal.Quotient.mk I (X 1))
  have hcomp : (MvPolynomial.aeval (R := K) ![x, y]) =
      (IsScalarTower.toAlgHom K Q L).comp (Ideal.Quotient.mkₐ K I) := by
    apply MvPolynomial.algHom_ext
    intro i; fin_cases i <;> (simp [x, y]; rfl)
  refine ⟨L, inferInstance, inferInstance, x, y, ?_, ?_⟩
  · ext p
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hcomp, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk]
    constructor
    · intro h
      have := (IsFractionRing.injective Q L) (h.trans (map_zero _).symm)
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    · intro h
      rw [Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]
  · rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Q) z
    have hmem : ∀ c : Q, algebraMap Q L c ∈ IntermediateField.adjoin K {x, y} := by
      intro c
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
      have : algebraMap Q L (Ideal.Quotient.mk I p) = MvPolynomial.aeval ![x, y] p := by
        rw [hcomp]; rfl
      rw [this]
      apply IntermediateField.algebra_adjoin_le_adjoin
      have hr : Set.range (![x, y] : Fin 2 → L) = {x, y} := by
        ext z; simp [Fin.exists_fin_two, eq_comm, or_comm]
      rw [← hr, Algebra.adjoin_range_eq_range_aeval]
      exact ⟨p, rfl⟩
    exact IntermediateField.div_mem _ (hmem a) (hmem b)

end PrivPCP.FF


namespace PrivPCP.FF

/-- the cube-root estimate -/
lemma cube_root_bound (N ab Y : ℝ) (hN : 0 ≤ N) (hab : 0 ≤ ab) (hY : 0 ≤ Y)
    (h : N * ab ^ 2 ≤ Y ^ 3) : N ^ ((1 : ℝ) / 3) * ab ^ ((2 : ℝ) / 3) ≤ Y := by
  set X := N ^ ((1 : ℝ) / 3) * ab ^ ((2 : ℝ) / 3) with hX
  have hX0 : 0 ≤ X := by positivity
  have hX3 : X ^ 3 = N * ab ^ 2 := by
    rw [hX, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (ab ^ _), ← Real.rpow_mul hN,
      ← Real.rpow_mul hab]
    norm_num
  by_contra hc
  push Not at hc
  have : Y ^ 3 < X ^ 3 := pow_lt_pow_left₀ hc hY (by norm_num)
  linarith

/-- the final arithmetic contradiction -/
lemma arith_contra (A B T H N n1 n2 k1 k2 eX eY dX dY G C c0 : ℝ)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hAT : A ≤ T) (hBT : B ≤ T) (hT : T ≤ c0 * H ^ 3 / N)
    (hH : 1 ≤ H) (hHN : H * H ≤ N)
    (h1 : H ≤ n1 - k1) (h2 : H ≤ n2 - k2) (heX : eX ≤ T) (heY : eY ≤ T)
    (hdX : dX ≤ k1 + eX) (hdY : dY ≤ k2 + eY)
    (hlow : n1 * B + n2 * A ≤ G + (2 * A * B + dX * B + dY * A))
    (hup : G ≤ C * (N ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3) + A * B))
    (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 8) (hc0M : c0 * (64 * (max C 1) ^ 3) ≤ 1) : False := by
  set M := max C 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hCM : C ≤ M := le_max_left _ _
  clear_value M
  have hH0 : 0 ≤ H := by linarith
  have hH2 : 0 < H * H := by positivity
  have hNpos : 0 < N := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hS0 : 0 ≤ A + B := by linarith
  have hTN : T * N ≤ c0 * H ^ 3 := by rwa [le_div_iff₀ hNpos] at hT
  have hTH : T ≤ c0 * H := by
    have q1 : T * (H * H) ≤ T * N := mul_le_mul_of_nonneg_left hHN hT0
    have q2 : T * (H * H) ≤ (c0 * H) * (H * H) := by
      have : c0 * H ^ 3 = (c0 * H) * (H * H) := by ring
      linarith
    exact le_of_mul_le_mul_right q2 hH2
  have hT8 : T ≤ H / 8 := by
    have := mul_le_mul_of_nonneg_right hc0' hH0
    linarith
  -- lower bound
  have hab1 : A * B ≤ T * B := mul_le_mul_of_nonneg_right hAT hB0
  have hab2 : A * B ≤ A * T := mul_le_mul_of_nonneg_left hBT hA0
  have p1 : dX * B ≤ (k1 + eX) * B := mul_le_mul_of_nonneg_right hdX hB0
  have p2 : dY * A ≤ (k2 + eY) * A := mul_le_mul_of_nonneg_right hdY hA0
  have p3 : (H - T) * B ≤ (n1 - k1 - eX) * B := mul_le_mul_of_nonneg_right (by linarith) hB0
  have p4 : (H - T) * A ≤ (n2 - k2 - eY) * A := mul_le_mul_of_nonneg_right (by linarith) hA0
  have hlow' : (H - 2 * T) * (A + B) ≤ G := by linarith
  have p5 : 2 * T * (A + B) ≤ H / 4 * (A + B) := mul_le_mul_of_nonneg_right (by linarith) hS0
  have hlow'' : 3 / 4 * (H * (A + B)) ≤ G := by linarith
  -- upper bound
  have hab0 : 0 ≤ A * B := by positivity
  have u1 : A * B ≤ T * (A + B) / 2 := by linarith
  have u2 : A * B ≤ (A + B) ^ 2 / 4 := by have := sq_nonneg (A - B); linarith
  have e1 : (A * B) ^ 2 ≤ T * (A + B) ^ 3 / 8 := by
    have := mul_le_mul u1 u2 hab0 (by positivity)
    calc (A * B) ^ 2 = A * B * (A * B) := by ring
      _ ≤ T * (A + B) / 2 * ((A + B) ^ 2 / 4) := this
      _ = T * (A + B) ^ 3 / 8 := by ring
  have hY0 : 0 ≤ H * (A + B) / (8 * M) := div_nonneg (mul_nonneg hH0 hS0) (by linarith)
  have hX : N ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3) ≤ H * (A + B) / (8 * M) := by
    apply cube_root_bound _ _ _ hNpos.le hab0 hY0
    have hW : 0 ≤ (A + B) ^ 3 := by positivity
    have e2 : N * (A * B) ^ 2 ≤ c0 * H ^ 3 * (A + B) ^ 3 / 8 := by
      have q1 := mul_le_mul_of_nonneg_left e1 hNpos.le
      have q2 := mul_le_mul_of_nonneg_right hTN hW
      have : N * (T * (A + B) ^ 3 / 8) = T * N * (A + B) ^ 3 / 8 := by ring
      linarith
    have e3 : c0 * H ^ 3 * (A + B) ^ 3 / 8 ≤ (H * (A + B) / (8 * M)) ^ 3 := by
      have hWW : 0 ≤ H ^ 3 * (A + B) ^ 3 := by positivity
      have eq : (H * (A + B) / (8 * M)) ^ 3 = H ^ 3 * (A + B) ^ 3 * (1 / (512 * M ^ 3)) := by
        field_simp; ring
      have hc : c0 / 8 ≤ 1 / (512 * M ^ 3) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      rw [eq]
      have := mul_le_mul_of_nonneg_left hc hWW
      calc c0 * H ^ 3 * (A + B) ^ 3 / 8 = H ^ 3 * (A + B) ^ 3 * (c0 / 8) := by ring
        _ ≤ _ := this
    linarith
  have hMc : M * c0 ≤ 1 / 64 := by
    have hM3 : M ≤ M ^ 3 := by
      have h2 : 1 ≤ M ^ 2 := one_le_pow₀ hM1
      have := mul_le_mul_of_nonneg_left h2 hM0.le
      have e : M * M ^ 2 = M ^ 3 := by ring
      linarith only [this, e]
    have := mul_le_mul_of_nonneg_left hM3 hc0.le
    linarith only [this, hc0M]
  have hABM : M * (A * B) ≤ H * (A + B) / 128 := by
    have q1 : A * B ≤ c0 * H * (A + B) / 2 := by
      have := mul_le_mul_of_nonneg_right hTH hS0
      linarith
    have q2 := mul_le_mul_of_nonneg_left q1 hM0.le
    have q3 : M * (c0 * H * (A + B) / 2) = (M * c0) * (H * (A + B)) / 2 := by ring
    have q4 := mul_le_mul_of_nonneg_right hMc (mul_nonneg hH0 hS0)
    linarith only [q2, q3, q4]
  have hX0 : 0 ≤ N ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3) := by positivity
  have hCM' : C * (N ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3) + A * B) ≤
      M * (N ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3) + A * B) :=
    mul_le_mul_of_nonneg_right hCM (by positivity)
  have h8 : M * (N ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3)) ≤ H * (A + B) / 8 := by
    calc M * (N ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3)) ≤ M * (H * (A + B) / (8 * M)) :=
          mul_le_mul_of_nonneg_left hX hM0.le
      _ = H * (A + B) / 8 := by
          have hMne : M ≠ 0 := hM0.ne'
          field_simp
  have hpos : 0 < H * (A + B) := by positivity
  have : M * (N ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3) + A * B) =
      M * (N ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3)) + M * (A * B) := by ring
  linarith only [this, hup, hCM', h8, hABM, hlow'', hpos]

end PrivPCP.FF


namespace PrivPCP.FF

lemma T_lt_H (T H N c0 : ℝ) (hT : T ≤ c0 * H ^ 3 / N) (hH : 1 ≤ H) (hHN : H * H ≤ N)
    (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 8) : T < H := by
  have hH0 : 0 ≤ H := by linarith
  have hNpos : 0 < N := by nlinarith
  have hH2 : 0 < H * H := by positivity
  have hTN : T * N ≤ c0 * H ^ 3 := by rwa [le_div_iff₀ hNpos] at hT
  by_contra hc
  push Not at hc
  have q1 : H * (H * H) ≤ T * N := mul_le_mul hc hHN hH2.le (by linarith)
  have q2 : c0 * H ^ 3 ≤ 1 / 8 * H ^ 3 := mul_le_mul_of_nonneg_right hc0' (by positivity)
  have e : H * (H * H) = H ^ 3 := by ring
  have h3 : 0 < H ^ 3 := by positivity
  linarith

end PrivPCP.FF

open PrivPCP PrivPCP.FF Classical MvPolynomial in
theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
      Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
      ∀ k₁ k₂ : ℕ, k₁ < Nat.card S₁ → k₂ < Nat.card S₂ →
      ∀ E P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q)), E ≠ 0 →
        (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤
          c₀ * ((min (Nat.card S₁ - k₁) (Nat.card S₂ - k₂) : ℕ) : ℝ) ^ 3 / ((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) →
        P.degreeOf 0 < k₁ + E.degreeOf 0 →
        P.degreeOf 1 < k₂ + E.degreeOf 1 →
        (∀ α ∈ S₁, ∃ R : Polynomial (AlgebraicClosure (ZMod q)),
          MvPolynomial.aeval (![Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (α : ZMod q)),
            Polynomial.X] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) P =
          MvPolynomial.aeval (![Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (α : ZMod q)),
            Polynomial.X] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) E * R) →
        (∀ β ∈ S₂, ∃ Cβ : Polynomial (AlgebraicClosure (ZMod q)),
          MvPolynomial.aeval (![Polynomial.X, Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
            (β : ZMod q))] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) P =
          MvPolynomial.aeval (![Polynomial.X, Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
            (β : ZMod q))] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) E * Cβ) →
        ∀ F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q)), Irreducible F → F ∣ E →
          0 < F.degreeOf 0 → 0 < F.degreeOf 1 → F ∣ P := by
  obtain ⟨C, HC⟩ := PrivPCP.lemma_4_13_gamma_upper
  set M := max C 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  set c0 : ℝ := min (1 / 8) (1 / (64 * M ^ 3)) with hc0def
  have hc0 : 0 < c0 := lt_min (by norm_num) (by positivity)
  have hc0' : c0 ≤ 1 / 8 := min_le_left _ _
  have hc0M : c0 * (64 * M ^ 3) ≤ 1 := by
    have h1 : c0 ≤ 1 / (64 * M ^ 3) := min_le_right _ _
    have h2 : 0 < 64 * M ^ 3 := by positivity
    rw [le_div_iff₀ h2] at h1
    exact h1
  refine ⟨c0, hc0, ?_⟩
  intro q _ S₁ S₂ hcop k₁ k₂ hk1 hk2 E P hE hmax hPX hPY hrow hcol F hF hFE hF0 hF1
  by_contra hFP
  obtain ⟨E', rfl⟩ := hFE
  have hFn : F ≠ 0 := hF.ne_zero
  have hE' : E' ≠ 0 := right_ne_zero_of_mul hE
  have d0 := degreeOf_mul_eq (n := (0 : Fin 2)) hFn hE'
  have d1 := degreeOf_mul_eq (n := (1 : Fin 2)) hFn hE'
  have rowsF : ∀ α ∈ S₁,
      MvPolynomial.aeval (![Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (α : ZMod q)),
        Polynomial.X] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) F ∣
      MvPolynomial.aeval (![Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (α : ZMod q)),
        Polynomial.X] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) P := by
    intro α hα
    obtain ⟨R, hR⟩ := hrow α hα
    rw [map_mul] at hR
    rw [hR]; exact (dvd_mul_right _ _).mul_right _
  have colsF : ∀ β ∈ S₂,
      MvPolynomial.aeval (![Polynomial.X, Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
        (β : ZMod q))] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) F ∣
      MvPolynomial.aeval (![Polynomial.X, Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
        (β : ZMod q))] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) P := by
    intro β hβ
    obtain ⟨R, hR⟩ := hcol β hβ
    rw [map_mul] at hR
    rw [hR]; exact (dvd_mul_right _ _).mul_right _
  obtain ⟨L, _, _, x, y, hker, hadj⟩ := exists_function_field F hF
  set n1 := Nat.card S₁ with hn1
  set n2 := Nat.card S₂ with hn2
  set h := min (n1 - k₁) (n2 - k₂) with hhdef
  have hh1 : h ≤ n1 - k₁ := Nat.min_le_left _ _
  have hh2 : h ≤ n2 - k₂ := Nat.min_le_right _ _
  have hhpos : 1 ≤ h := by omega
  have hHr : (1 : ℝ) ≤ h := by exact_mod_cast hhpos
  have hHN : (h : ℝ) * h ≤ ((n1 * n2 : ℕ) : ℝ) := by
    have : h * h ≤ n1 * n2 := Nat.mul_le_mul (by omega) (by omega)
    exact_mod_cast this
  set T : ℝ := max ((F * E').degreeOf 0 : ℝ) ((F * E').degreeOf 1 : ℝ) with hTdef
  have hTlt := T_lt_H T h _ c0 hmax hHr hHN hc0 hc0'
  have hcardq : ∀ S : Subgroup (ZMod q)ˣ, Nat.card S ≤ q - 1 := by
    intro S
    have := Subgroup.card_le_card_group S
    rwa [Nat.card_eq_fintype_card (α := (ZMod q)ˣ), ZMod.card_units] at this
  have haT : ((F.degreeOf 0 : ℕ) : ℝ) ≤ T := by
    refine le_trans ?_ (le_max_left _ _); rw [d0]; push_cast; linarith
  have hbT : ((F.degreeOf 1 : ℕ) : ℝ) ≤ T := by
    refine le_trans ?_ (le_max_right _ _); rw [d1]; push_cast; linarith
  have haq : F.degreeOf 0 < q := by
    have : ((F.degreeOf 0 : ℕ) : ℝ) < h := lt_of_le_of_lt haT hTlt
    have : F.degreeOf 0 < h := by exact_mod_cast this
    have := hcardq S₁
    have := (Fact.out : q.Prime).two_le
    omega
  have hbq : F.degreeOf 1 < q := by
    have : ((F.degreeOf 1 : ℕ) : ℝ) < h := lt_of_le_of_lt hbT hTlt
    have : F.degreeOf 1 < h := by exact_mod_cast this
    have := hcardq S₂
    have := (Fact.out : q.Prime).two_le
    omega
  have hlowE := PrivPCP.lemma_4_13_zero_count q S₁ S₂ F P hF hF0 hF1 hFP rowsF colsF L x y hker hadj
  obtain ⟨hfin, hup⟩ := HC q S₁ S₂ hcop F hF hF0 hF1 haq hbq L x y hker hadj
  set Γ := PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y n1 n2 with hΓ
  have hΓ' : Γ = ((Γ.toNat : ℕ) : ℕ∞) := (ENat.coe_toNat hfin).symm
  rw [hΓ', ← Nat.cast_add, Nat.cast_le] at hlowE
  have hlowR : ((n1 * F.degreeOf 1 + n2 * F.degreeOf 0 : ℕ) : ℝ) ≤
      ((Γ.toNat + (2 * F.degreeOf 0 * F.degreeOf 1 + P.degreeOf 0 * F.degreeOf 1 +
        P.degreeOf 1 * F.degreeOf 0) : ℕ) : ℝ) := by exact_mod_cast hlowE
  push_cast at hlowR hup
  have hk1r : (h : ℝ) ≤ n1 - k₁ := by
    have : ((h : ℕ) : ℝ) ≤ ((n1 - k₁ : ℕ) : ℝ) := by exact_mod_cast hh1
    rwa [Nat.cast_sub hk1.le] at this
  have hk2r : (h : ℝ) ≤ n2 - k₂ := by
    have : ((h : ℕ) : ℝ) ≤ ((n2 - k₂ : ℕ) : ℝ) := by exact_mod_cast hh2
    rwa [Nat.cast_sub hk2.le] at this
  have hdX : ((P.degreeOf 0 : ℕ) : ℝ) ≤ k₁ + ((F * E').degreeOf 0 : ℝ) := by
    exact_mod_cast hPX.le
  have hdY : ((P.degreeOf 1 : ℕ) : ℝ) ≤ k₂ + ((F * E').degreeOf 1 : ℝ) := by
    exact_mod_cast hPY.le
  exact arith_contra (F.degreeOf 0) (F.degreeOf 1) T h ((n1 * n2 : ℕ) : ℝ) n1 n2 k₁ k₂
    ((F * E').degreeOf 0) ((F * E').degreeOf 1) (P.degreeOf 0) (P.degreeOf 1) (Γ.toNat) C c0
    (by exact_mod_cast hF0) (by exact_mod_cast hF1) haT hbT hmax hHr hHN hk1r hk2r
    (le_max_left _ _) (le_max_right _ _) hdX hdY (by linarith) (by push_cast; exact hup)
    hc0 hc0' hc0M


