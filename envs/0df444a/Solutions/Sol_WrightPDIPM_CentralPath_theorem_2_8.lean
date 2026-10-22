-- Prove2me | solution 1 for WrightPDIPM.CentralPath.theorem_2_8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:57:29.168957+00:00
-- url     : https://prove2.me/submissions/58497fd8-53ed-4c5b-a52a-3e9dfb21f367

import Mathlib
import Definitions.Def_WrightPDIPM_CentralPath_LP

open WrightPDIPM.CentralPath
open Filter Topology Matrix

theorem g70wr_foc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (τ : ℝ) (x s : Fin n → ℝ) (hq : (x, s) ∈ Hcirc A b c)
    (hmin : IsLocalMinOn (ftau τ) (Hcirc A b c) (x, s))
    (dx ds : Fin n → ℝ) (dl : Fin m → ℝ) (h1 : A *ᵥ dx = 0) (h2 : Aᵀ *ᵥ dl + ds = 0) :
    1 / τ * ∑ j, (dx j * s j + x j * ds j) - ∑ j, (dx j * s j + x j * ds j) / (x j * s j) = 0 := by
  obtain ⟨lam, ⟨hA, hx⟩, hd, hs⟩ := hq
  simp only at hA hx hd hs
  set γ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) := fun t => (x + t • dx, s + t • ds) with hγ
  have hγ0 : γ 0 = (x, s) := by simp [hγ]
  have hγc : Continuous γ := by rw [hγ]; fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ Hcirc A b c := by
    have ex : ∀ j, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < x j + t * dx j := fun j => by
      have hc : Continuous (fun t : ℝ => x j + t * dx j) := by fun_prop
      exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using hx j)
    have es : ∀ j, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < s j + t * ds j := fun j => by
      have hc : Continuous (fun t : ℝ => s j + t * ds j) := by fun_prop
      exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using hs j)
    filter_upwards [eventually_all.2 ex, eventually_all.2 es] with t htx hts
    refine ⟨lam + t • dl, ⟨?_, fun j => ?_⟩, ⟨?_, fun j => ?_⟩⟩
    · simp [hγ, mulVec_add, mulVec_smul, hA, h1]
    · simpa [hγ] using htx j
    · simp only [hγ]
      rw [mulVec_add, mulVec_smul]
      calc Aᵀ *ᵥ lam + t • (Aᵀ *ᵥ dl) + (s + t • ds) = (Aᵀ *ᵥ lam + s) + t • (Aᵀ *ᵥ dl + ds) := by
            rw [smul_add]; abel
        _ = c := by rw [hd, h2, smul_zero, add_zero]
    · simpa [hγ] using hts j
  have htend : Tendsto γ (𝓝 0) (𝓝[Hcirc A b c] (γ 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hγc.tendsto 0, hev⟩
  rw [← hγ0] at hmin
  have hloc : IsLocalMin (ftau τ ∘ γ) 0 := hmin.comp_tendsto htend
  have hfun : ftau τ ∘ γ = fun t => 1 / τ * ∑ j, (x j + t * dx j) * (s j + t * ds j)
      - ∑ j, Real.log ((x j + t * dx j) * (s j + t * ds j)) := by
    funext t; simp [ftau, hγ, dotProduct]
  have hp : ∀ j, HasDerivAt (fun t : ℝ => (x j + t * dx j) * (s j + t * ds j))
      (dx j * s j + x j * ds j) 0 := fun j => by
    have a1 : HasDerivAt (fun t : ℝ => x j + t * dx j) (dx j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dx j)).const_add (x j)
    have a2 : HasDerivAt (fun t : ℝ => s j + t * ds j) (ds j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ds j)).const_add (s j)
    have h := a1.mul a2
    simp only [zero_mul, add_zero] at h
    exact h
  have hD : HasDerivAt (ftau τ ∘ γ) (1 / τ * ∑ j, (dx j * s j + x j * ds j)
      - ∑ j, (dx j * s j + x j * ds j) / (x j * s j)) 0 := by
    rw [hfun]
    apply HasDerivAt.sub
    · exact (HasDerivAt.fun_sum fun j _ => hp j).const_mul _
    · apply HasDerivAt.fun_sum
      intro j _
      have := (hp j).log (by simp; exact ⟨(hx j).ne', (hs j).ne'⟩)
      simpa using this
  exact hloc.hasDerivAt_eq_zero hD

theorem g70wr_cpt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (x s : Fin n → ℝ) (hq : (x, s) ∈ Hcirc A b c)
    (hmin : IsLocalMinOn (ftau τ) (Hcirc A b c) (x, s)) : ∀ j, x j * s j = τ := by
  have hq' := hq
  obtain ⟨lam, ⟨hA, hx⟩, hd, hs⟩ := hq'
  simp only at hA hx hd hs
  set d : Fin n → ℝ := fun j => x j / τ - 1 / s j with hd'
  -- A d = 0
  have hAd : A *ᵥ d = 0 := by
    have h := g70wr_foc A b c τ x s hq hmin 0 (-(Aᵀ *ᵥ (A *ᵥ d))) (A *ᵥ d) (by simp) (by simp)
    have e : ∀ j, (0 : Fin n → ℝ) j * s j + x j * (-(Aᵀ *ᵥ (A *ᵥ d))) j =
        x j * (-(Aᵀ *ᵥ (A *ᵥ d))) j := fun j => by simp
    simp only [e] at h
    have e2 : ∀ w : Fin n → ℝ, 1 / τ * ∑ j, x j * (-w) j
        - ∑ j, x j * (-w) j / (x j * s j) = -(d ⬝ᵥ w) := fun w => by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show d j = x j / τ - 1 / s j from rfl]
      have := (hx j).ne'; have := (hs j).ne'; have := hτ.ne'
      simp only [Pi.neg_apply]
      field_simp; ring
    rw [e2] at h
    have e3 : d ⬝ᵥ (Aᵀ *ᵥ (A *ᵥ d)) = (A *ᵥ d) ⬝ᵥ (A *ᵥ d) := by
      rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
    rw [e3] at h
    have h0 : (A *ᵥ d) ⬝ᵥ (A *ᵥ d) = 0 := by linarith
    exact dotProduct_self_eq_zero.mp h0
  have h := g70wr_foc A b c τ x s hq hmin d 0 0 hAd (by simp)
  simp only [Pi.zero_apply, mul_zero, add_zero] at h
  have e : ∀ j, (x j * s j - τ) ^ 2 / (τ ^ 2 * (x j * s j)) =
      1 / τ * (d j * s j) - d j * s j / (x j * s j) := fun j => by
    have := (hx j).ne'; have := (hs j).ne'; have := hτ.ne'
    simp only [hd']; field_simp
  have hsum : ∑ j, (x j * s j - τ) ^ 2 / (τ ^ 2 * (x j * s j)) = 0 := by
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (x j * s j - τ) ^ 2 / (τ ^ 2 * (x j * s j)) := fun j _ => by
    have := mul_pos (hx j) (hs j); positivity
  intro j
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j (Finset.mem_univ j)
  have hpos : 0 < τ ^ 2 * (x j * s j) := by have := mul_pos (hx j) (hs j); positivity
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; linarith
  · linarith

theorem g70wr_wd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hx : A *ᵥ x = b)
    (hd : Aᵀ *ᵥ lam + s = c) : c ⬝ᵥ x = b ⬝ᵥ lam + s ⬝ᵥ x := by
  rw [← hd, ← hx, add_dotProduct, mulVec_transpose, dotProduct_comm (A *ᵥ x) lam, dotProduct_mulVec]

theorem g70wr_orth {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x x' : Fin n → ℝ) (l l' : Fin m → ℝ) (s s' : Fin n → ℝ) (hx : A *ᵥ x = b)
    (hx' : A *ᵥ x' = b) (hd : Aᵀ *ᵥ l + s = c) (hd' : Aᵀ *ᵥ l' + s' = c) :
    x ⬝ᵥ s' + x' ⬝ᵥ s = x ⬝ᵥ s + x' ⬝ᵥ s' := by
  have h1 := g70wr_wd A b c x l s hx hd
  have h2 := g70wr_wd A b c x l' s' hx hd'
  have h3 := g70wr_wd A b c x' l s hx' hd
  have h4 := g70wr_wd A b c x' l' s' hx' hd'
  rw [dotProduct_comm x s', dotProduct_comm x' s, dotProduct_comm x s, dotProduct_comm x' s']
  linarith

theorem g70wr_uniq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (q1 q2 : (Fin n → ℝ) × (Fin n → ℝ)) (h1 : q1 ∈ Hcirc A b c)
    (h2 : q2 ∈ Hcirc A b c) (e1 : ∀ j, q1.1 j * q1.2 j = τ) (e2 : ∀ j, q2.1 j * q2.2 j = τ) :
    q1 = q2 := by
  obtain ⟨l1, ⟨hA1, hx1⟩, hd1, hs1⟩ := h1
  obtain ⟨l2, ⟨hA2, hx2⟩, hd2, hs2⟩ := h2
  have o := g70wr_orth A b c q1.1 q2.1 l1 l2 q1.2 q2.2 hA1 hA2 hd1 hd2
  have hsum : ∑ j, (q1.1 j - q2.1 j) * (q1.2 j - q2.2 j) = 0 := by
    simp only [dotProduct] at o
    have : ∀ j, (q1.1 j - q2.1 j) * (q1.2 j - q2.2 j) =
        q1.1 j * q1.2 j + q2.1 j * q2.2 j - (q1.1 j * q2.2 j + q2.1 j * q1.2 j) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    linarith
  have hterm : ∀ j, (q1.1 j - q2.1 j) * (q1.2 j - q2.2 j) = -(τ * (q1.1 j - q2.1 j) ^ 2) / (q1.1 j * q2.1 j) := fun j => by
    have a1 := (hx1 j).ne'; have a2 := (hx2 j).ne'
    have s1 : q1.2 j = τ / q1.1 j := by rw [← e1 j]; field_simp
    have s2 : q2.2 j = τ / q2.1 j := by rw [← e2 j]; field_simp
    rw [s1, s2]; field_simp; ring
  have hnp : ∀ j ∈ Finset.univ, (q1.1 j - q2.1 j) * (q1.2 j - q2.2 j) ≤ 0 := fun j _ => by
    rw [hterm j]
    apply div_nonpos_of_nonpos_of_nonneg
    · have := sq_nonneg (q1.1 j - q2.1 j); nlinarith
    · exact (mul_pos (hx1 j) (hx2 j)).le
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hnp).1 hsum
  have hx : q1.1 = q2.1 := by
    funext j
    have := hz j (Finset.mem_univ j)
    rw [hterm j, div_eq_zero_iff] at this
    rcases this with h | h
    · have : (q1.1 j - q2.1 j) ^ 2 = 0 := by
        have := mul_eq_zero.mp (neg_eq_zero.mp h); rcases this with h' | h'
        · linarith
        · exact h'
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this; linarith
    · exact absurd h (mul_pos (hx1 j) (hx2 j)).ne'
  have hs : q1.2 = q2.2 := by
    funext j
    have a := e1 j; have b' := e2 j; rw [hx] at a
    have := (hx2 j).ne'
    have : q1.2 j = τ / q2.1 j := by rw [← a]; field_simp
    rw [this, ← b']; field_simp
  exact Prod.ext hx hs

theorem g70wr_phi (τ t : ℝ) (hτ : 0 < τ) (ht : 0 < t) (k : ℝ) (hk : 0 < k) :
    t / (k * τ) - 1 + Real.log (k * τ) ≥ Real.log t := by
  have h := Real.log_le_sub_one_of_pos (div_pos ht (mul_pos hk hτ))
  rw [Real.log_div ht.ne' (mul_pos hk hτ).ne'] at h
  linarith

theorem g70wr_fsum {n : ℕ} (τ : ℝ) (x s : Fin n → ℝ) :
    ftau τ (x, s) = ∑ j, (x j * s j / τ - Real.log (x j * s j)) := by
  simp only [ftau, dotProduct, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1; refine Finset.sum_congr rfl fun j _ => ?_; ring

set_option maxHeartbeats 1000000 in
theorem g70wr_exist {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hFo : (Fo A b c).Nonempty) (τ : ℝ) (hτ : 0 < τ) :
    ∃ q ∈ Hcirc A b c, IsMinOn (ftau τ) (Hcirc A b c) q := by
  classical
  obtain ⟨⟨x0, l0, s0⟩, ⟨hA0, hx0⟩, hd0, hs0⟩ := hFo
  simp only at hA0 hx0 hd0 hs0
  have hq0 : (x0, s0) ∈ Hcirc A b c := ⟨l0, ⟨hA0, hx0⟩, hd0, hs0⟩
  set M0 := ftau τ (x0, s0) with hM0
  set mm := 1 - Real.log τ with hmm
  set m2 := 1 - Real.log (2 * τ) with hm2
  set M1 := M0 - n * mm + mm with hM1
  set a := Real.exp (-M1) with ha
  set P := 2 * τ * (M0 - n * m2) with hP
  set K := P + x0 ⬝ᵥ s0 with hK
  set U := ∑ i, (|K| / s0 i + |K| / x0 i) + 1 with hU
  set ℓ := a / U with hℓ
  have hU1 : 1 ≤ U := by
    have : 0 ≤ ∑ i, (|K| / s0 i + |K| / x0 i) := Finset.sum_nonneg fun i _ => by
      have := hx0 i; have := hs0 i; positivity
    linarith
  have hℓ0 : 0 < ℓ := div_pos (Real.exp_pos _) (by linarith)
  -- bounds on the sublevel set
  have hbnd : ∀ x s, (x, s) ∈ Hcirc A b c → ftau τ (x, s) ≤ M0 →
      ∀ j, ℓ ≤ x j ∧ x j ≤ U ∧ ℓ ≤ s j ∧ s j ≤ U := by
    intro x s hq hf
    obtain ⟨l, ⟨hA, hx⟩, hd, hs⟩ := hq
    simp only at hA hx hd hs
    rw [g70wr_fsum] at hf
    have ht : ∀ j, 0 < x j * s j := fun j => mul_pos (hx j) (hs j)
    have hφ1 : ∀ j, mm ≤ x j * s j / τ - Real.log (x j * s j) := fun j => by
      have := g70wr_phi τ (x j * s j) hτ (ht j) 1 one_pos
      simp only [one_mul] at this; rw [hmm]; linarith
    have hφ2 : ∀ j, x j * s j / (2 * τ) + m2 ≤ x j * s j / τ - Real.log (x j * s j) := fun j => by
      have := g70wr_phi τ (x j * s j) hτ (ht j) 2 two_pos
      have e : x j * s j / τ = 2 * (x j * s j / (2 * τ)) := by field_simp
      rw [hm2, e]; linarith
    -- each term bounded
    have hM1b : ∀ j, x j * s j / τ - Real.log (x j * s j) ≤ M1 := fun j => by
      have h1 := Finset.single_le_sum (f := fun i => x i * s i / τ - Real.log (x i * s i) - mm)
        (fun i _ => by have := hφ1 i; linarith) (Finset.mem_univ j)
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at h1
      have hf' := hf
      rw [Finset.sum_sub_distrib] at hf'
      rw [hM1]; linarith
    have hlow : ∀ j, a ≤ x j * s j := fun j => by
      have h := hM1b j
      have : -M1 ≤ Real.log (x j * s j) := by
        have := div_nonneg (ht j).le hτ.le; linarith
      calc a = Real.exp (-M1) := rfl
        _ ≤ Real.exp (Real.log (x j * s j)) := Real.exp_le_exp.mpr this
        _ = x j * s j := Real.exp_log (ht j)
    have hsumP : x ⬝ᵥ s ≤ P := by
      have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hφ2 i)
      rw [Finset.sum_add_distrib, ← Finset.sum_div] at h
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      have h2 : (∑ i, x i * s i) / (2 * τ) ≤ M0 - n * m2 := by linarith
      rw [div_le_iff₀ (by positivity)] at h2
      simp only [dotProduct]; rw [hP]; linarith
    have o := g70wr_orth A b c x x0 l l0 s s0 hA hA0 hd hd0
    have n1 : 0 ≤ x0 ⬝ᵥ s := Finset.sum_nonneg fun i _ => mul_nonneg (hx0 i).le (hs i).le
    have n2 : 0 ≤ x ⬝ᵥ s0 := Finset.sum_nonneg fun i _ => mul_nonneg (hx i).le (hs0 i).le
    have hxs0 : x ⬝ᵥ s0 ≤ K := by rw [hK]; linarith
    have hx0s : x0 ⬝ᵥ s ≤ K := by rw [hK]; linarith
    have hUi : ∀ i, |K| / s0 i + |K| / x0 i ≤ U := fun i => by
      have := Finset.single_le_sum (f := fun i => |K| / s0 i + |K| / x0 i)
        (fun i _ => by have := hx0 i; have := hs0 i; positivity) (Finset.mem_univ i)
      rw [hU]; linarith
    have hxU : ∀ j, x j ≤ U := fun j => by
      have h1 := Finset.single_le_sum (f := fun i => x i * s0 i)
        (fun i _ => mul_nonneg (hx i).le (hs0 i).le) (Finset.mem_univ j)
      have : x j ≤ |K| / s0 j := by
        rw [le_div_iff₀ (hs0 j)]; have := le_abs_self K
        simp only [dotProduct] at hxs0; linarith
      have := hUi j; have : 0 ≤ |K| / x0 j := by have := hx0 j; positivity
      linarith
    have hsU : ∀ j, s j ≤ U := fun j => by
      have h1 := Finset.single_le_sum (f := fun i => x0 i * s i)
        (fun i _ => mul_nonneg (hx0 i).le (hs i).le) (Finset.mem_univ j)
      have : s j ≤ |K| / x0 j := by
        rw [le_div_iff₀ (hx0 j)]; have := le_abs_self K
        simp only [dotProduct] at hx0s; linarith
      have := hUi j; have : 0 ≤ |K| / s0 j := by have := hs0 j; positivity
      linarith
    intro j
    refine ⟨?_, hxU j, ?_, hsU j⟩
    · rw [hℓ, div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left (hsU j) (hx j).le
      linarith [hlow j]
    · rw [hℓ, div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_right (hxU j) (hs j).le
      linarith [hlow j]
  -- compact set
  set V := LinearMap.range (Matrix.mulVecLin Aᵀ) with hV
  set Kset : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {q | A *ᵥ q.1 = b} ∩ {q | c - q.2 ∈ V} ∩
      ⋂ j, {q | ℓ ≤ q.1 j ∧ q.1 j ≤ U ∧ ℓ ≤ q.2 j ∧ q.2 j ≤ U} with hKset
  have hmemV : ∀ s : Fin n → ℝ, (∃ l, Aᵀ *ᵥ l + s = c) ↔ c - s ∈ V := fun s => by
    constructor
    · rintro ⟨l, hl⟩; exact ⟨l, by simp only [Matrix.mulVecLin_apply]; rw [← hl]; abel⟩
    · rintro ⟨l, hl⟩; exact ⟨l, by simp only [Matrix.mulVecLin_apply] at hl; rw [hl]; abel⟩
  have hcl : IsClosed Kset := by
    refine IsClosed.inter (IsClosed.inter ?_ ?_) (isClosed_iInter fun j => ?_)
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact (Submodule.closed_of_finiteDimensional V).preimage (by fun_prop)
    · simp only [Set.setOf_and]
      refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)) <;>
        exact isClosed_le (by fun_prop) (by fun_prop)
  have hbd : Bornology.IsBounded Kset := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨U, fun q hq => ?_⟩
    have hq' := Set.mem_iInter.mp hq.2
    have hU0 : 0 ≤ U := by linarith
    rw [Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg hU0, pi_norm_le_iff_of_nonneg hU0]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · obtain ⟨h1, h2, -, -⟩ := hq' j
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    · obtain ⟨-, -, h1, h2⟩ := hq' j
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hcpt : IsCompact Kset := Metric.isCompact_of_isClosed_isBounded hcl hbd
  have hsub : ∀ q ∈ Hcirc A b c, ftau τ q ≤ M0 → q ∈ Kset := by
    rintro ⟨x, s⟩ hq hf
    have hb := hbnd x s hq hf
    obtain ⟨l, ⟨hA, hx⟩, hd, hs⟩ := hq
    exact ⟨⟨hA, (hmemV s).1 ⟨l, hd⟩⟩, Set.mem_iInter.mpr fun j => hb j⟩
  have hKH : ∀ q ∈ Kset, q ∈ Hcirc A b c := by
    rintro ⟨x, s⟩ ⟨⟨hA, hV'⟩, hbx⟩
    obtain ⟨l, hl⟩ := (hmemV s).2 hV'
    have hbx' := Set.mem_iInter.mp hbx
    exact ⟨l, ⟨hA, fun j => lt_of_lt_of_le hℓ0 (hbx' j).1⟩, hl,
      fun j => lt_of_lt_of_le hℓ0 (hbx' j).2.2.1⟩
  have hcont : ContinuousOn (ftau τ) Kset := by
    have e : ftau τ = fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
        1 / τ * (∑ j, q.1 j * q.2 j) - ∑ j, Real.log (q.1 j * q.2 j) := by
      funext q; simp [ftau, dotProduct]
    rw [e]
    refine ContinuousOn.sub (Continuous.continuousOn (by fun_prop)) ?_
    refine continuousOn_finsetSum _ fun j _ => ContinuousOn.log (by fun_prop) fun q hq => ?_
    have := hKH q hq
    obtain ⟨l, ⟨-, hx⟩, -, hs⟩ := this
    exact (mul_pos (hx j) (hs j)).ne'
  have hne : (x0, s0) ∈ Kset := hsub _ hq0 le_rfl
  obtain ⟨qs, hqs, hmin⟩ := hcpt.exists_isMinOn ⟨_, hne⟩ hcont
  refine ⟨qs, hKH qs hqs, fun q hq => ?_⟩
  by_cases hf : ftau τ q ≤ M0
  · exact hmin (hsub q hq hf)
  · have := hmin hne
    simp only [Set.mem_setOf_eq] at this ⊢
    push Not at hf
    linarith


open Matrix

/-- Wright, *Primal-Dual Interior-Point Methods*, SIAM 1997, p. 39, Theorem 2.8. Suppose
`F° ≠ ∅` and `τ > 0`. Then `f_τ` has a unique local minimizer in `H°` (local relative to
`H°`, which is relatively open in an affine subspace), and the central path conditions (2.25)
have a solution `(x, λ, s)`. No rank assumption on `A`; `λ` is not claimed unique. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hFo : (Fo A b c).Nonempty) (τ : ℝ) (hτ : 0 < τ) :
    (∃! q : (Fin n → ℝ) × (Fin n → ℝ), q ∈ Hcirc A b c ∧ IsLocalMinOn (ftau τ) (Hcirc A b c) q) ∧
    ∃ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ), CentralPathConditions A b c τ x lam s := by
  obtain ⟨q, hq, hmin⟩ := g70wr_exist A b c hFo τ hτ
  have hcp := g70wr_cpt A b c τ hτ q.1 q.2 hq hmin.localize
  refine ⟨⟨q, ⟨hq, hmin.localize⟩, fun q' ⟨hq', hloc'⟩ => ?_⟩, ?_⟩
  · have h' := g70wr_cpt A b c τ hτ q'.1 q'.2 hq' hloc'
    exact g70wr_uniq A b c τ hτ q' q hq' hq h' hcp
  · obtain ⟨l, ⟨hA, hx⟩, hd, hs⟩ := hq
    exact ⟨q.1, l, q.2, hd, hA, hcp, hx, hs⟩


