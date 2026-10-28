-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P06.physical_degradingMap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:01:11.964201+00:00
-- url     : https://prove2.me/submissions/488ba6c4-14e7-45d3-a893-918b04e0c20e

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

namespace X7L3DG

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity productCoeff)

def X7_ι (k : ℕ) : NumberString 1 := fun _ => k

lemma X7_ι_eq (a : NumberString 1) : a = X7_ι (a 0) := by
  funext i; rw [Subsingleton.elim i 0]; rfl

noncomputable def X7_Bc (η : ℝ) (m l : ℕ) : ℝ :=
  Real.sqrt ((m + l).choose m : ℝ) * Real.sqrt η ^ m * Real.sqrt (1 - η) ^ l

lemma X7_beam_vac (η : ℝ) (m l : ℕ) : beamCoefficient η m l (m + l) 0 = X7_Bc η m l := by
  unfold beamCoefficient X7_Bc
  rw [if_pos (by simp)]
  rw [Finset.sum_eq_single m]
  · simp only [le_refl, Nat.sub_self, true_and, Nat.choose_zero_right, Nat.cast_one, mul_one,
      pow_zero, add_zero, Nat.factorial_zero, if_true]
    rw [show m + l - m = l by omega]
    have hc : ((m + l).choose m : ℝ) = (m + l).factorial / (m.factorial * l.factorial) := by
      rw [Nat.choose_eq_factorial_div_factorial (by omega), Nat.cast_div]
      · rw [show m + l - m = l by omega]; push_cast; ring
      · rw [show m + l - m = l by omega]; exact Nat.factorial_mul_factorial_dvd_factorial_add m l
      · rw [show m + l - m = l by omega]; positivity
    have hpos : (0:ℝ) < ((m + l).choose m : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hinv : ((m.factorial : ℝ) * l.factorial) / ((m + l).factorial) =
        (((m + l).choose m : ℝ))⁻¹ := by
      rw [hc]; field_simp
    rw [hinv, Real.sqrt_inv]
    have hs : Real.sqrt ((m + l).choose m : ℝ) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    have hsq : Real.sqrt ((m + l).choose m : ℝ) ^ 2 = ((m + l).choose m : ℝ) :=
      Real.sq_sqrt hpos.le
    field_simp
    rw [hsq]
  · intro u _ hu
    rw [if_neg (by omega)]
  · intro h; simp at h

lemma X7_beam_ne (η : ℝ) (m l p : ℕ) (h : m + l ≠ p) : beamCoefficient η m l p 0 = 0 := by
  unfold beamCoefficient; rw [if_neg (by omega)]

lemma X7_blockBeam (η : ℝ) (out inp : NumberString 1 × NumberString 1) :
    blockBeam 1 η out inp = (beamCoefficient η (out.1 0) (out.2 0) (inp.1 0) (inp.2 0) : ℂ) := by
  simp [blockBeam]

lemma X7_jm (η : ℝ) (X : FockKernel 1) (u v : NumberString 1 × NumberString 1) :
    jointMix 1 η X (vacuum 1) u v =
      ((X7_Bc η (u.1 0) (u.2 0) * X7_Bc η (v.1 0) (v.2 0) : ℝ) : ℂ) *
        X (X7_ι (u.1 0 + u.2 0)) (X7_ι (v.1 0 + v.2 0)) := by
  unfold jointMix
  have hterm : ∀ a b : NumberString 1 × NumberString 1,
      (a ≠ (X7_ι (u.1 0 + u.2 0), 0) ∨ b ≠ (X7_ι (v.1 0 + v.2 0), 0)) →
      blockBeam 1 η u a * productCoeff X (vacuum 1) a b * star (blockBeam 1 η v b) = 0 := by
    intro a b hab
    simp only [productCoeff, vacuum]
    by_cases h2 : a.2 = 0 ∧ b.2 = 0
    · rw [if_pos h2]
      rcases hab with ha | hb
      · have : a.1 0 ≠ u.1 0 + u.2 0 := by
          intro h; apply ha; rw [Prod.ext_iff]; refine ⟨?_, h2.1⟩
          rw [X7_ι_eq a.1, h]
        have hz : a.2 0 = 0 := by rw [h2.1]; rfl
        rw [X7_blockBeam, hz, X7_beam_ne _ _ _ _ (fun h' => this h'.symm)]
        simp
      · have : b.1 0 ≠ v.1 0 + v.2 0 := by
          intro h; apply hb; rw [Prod.ext_iff]; refine ⟨?_, h2.2⟩
          rw [X7_ι_eq b.1, h]
        have hz : b.2 0 = 0 := by rw [h2.2]; rfl
        rw [X7_blockBeam η v b, hz, X7_beam_ne _ _ _ _ (fun h' => this h'.symm)]
        simp
    · rw [if_neg h2]; simp
  rw [tsum_eq_single (X7_ι (u.1 0 + u.2 0), 0)]
  · rw [tsum_eq_single (X7_ι (v.1 0 + v.2 0), 0)]
    · simp only [productCoeff, vacuum, and_self, if_true, mul_one, X7_blockBeam]
      simp only [Pi.zero_apply, X7_ι]
      rw [X7_beam_vac, X7_beam_vac]
      push_cast
      simp only [Complex.star_def, Complex.conj_ofReal]
      ring
    · intro b hb; exact hterm _ _ (Or.inr hb)
  · intro a ha
    exact (tsum_congr (fun b => hterm _ b (Or.inl ha))).trans tsum_zero


lemma X7_reidx (f : ℕ → ℂ) : ∑' e : NumberString 1, f (e 0) = ∑' k : ℕ, f k := by
  rw [← (Equiv.funUnique (Fin 1) ℕ).symm.tsum_eq]
  simp

lemma X7_bob (η : ℝ) (X : FockKernel 1) (a b : NumberString 1) :
    pureLoss 1 η X a b = ∑' k : ℕ, ((X7_Bc η (a 0) k * X7_Bc η (b 0) k : ℝ) : ℂ) *
      X (X7_ι (a 0 + k)) (X7_ι (b 0 + k)) := by
  unfold pureLoss bobMarginal
  simp only [X7_jm]
  exact X7_reidx (fun k => ((X7_Bc η (a 0) k * X7_Bc η (b 0) k : ℝ) : ℂ) *
      X (X7_ι (a 0 + k)) (X7_ι (b 0 + k)))

lemma X7_eve (η : ℝ) (X : FockKernel 1) (a b : NumberString 1) :
    charlieMarginal (broadcast 1 η X) a b = ∑' k : ℕ, ((X7_Bc η k (a 0) * X7_Bc η k (b 0) : ℝ) : ℂ) *
      X (X7_ι (k + a 0)) (X7_ι (k + b 0)) := by
  unfold broadcast charlieMarginal
  simp only [X7_jm]
  exact X7_reidx (fun k => ((X7_Bc η k (a 0) * X7_Bc η k (b 0) : ℝ) : ℂ) *
      X (X7_ι (k + a 0)) (X7_ι (k + b 0)))

lemma X7_Bc_nonneg (η : ℝ) (m l : ℕ) : 0 ≤ X7_Bc η m l := by
  unfold X7_Bc; positivity

lemma X7_Bc_le_one {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (m l : ℕ) : X7_Bc η m l ≤ 1 := by
  have hsq : X7_Bc η m l ^ 2 = ((m + l).choose m : ℝ) * η ^ m * (1 - η) ^ l := by
    unfold X7_Bc
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Real.sq_sqrt (by positivity)]
    rw [mul_comm m 2, mul_comm l 2, pow_mul, pow_mul, Real.sq_sqrt h0, Real.sq_sqrt (by linarith)]
  have hle : ((m + l).choose m : ℝ) * η ^ m * (1 - η) ^ l ≤ 1 := by
    have h := add_pow η (1 - η) (m + l)
    rw [show η + (1 - η) = 1 by ring, one_pow] at h
    have := Finset.single_le_sum (f := fun k => η ^ k * (1 - η) ^ (m + l - k) * ((m + l).choose k : ℝ))
      (s := Finset.range (m + l + 1)) (fun k _ => by have : 0 ≤ 1 - η := by linarith
                                                     positivity)
      (Finset.mem_range.2 (show m < m + l + 1 by omega))
    simp only [show m + l - m = l by omega] at this
    have e : ((m + l).choose m : ℝ) * η ^ m * (1 - η) ^ l = η ^ m * (1 - η) ^ l * ((m + l).choose m : ℝ) := by ring
    linarith
  have := X7_Bc_nonneg η m l
  nlinarith

lemma X7_choose_id (m e f : ℕ) :
    ((m + e).choose m : ℝ) * ((m + e + f).choose (m + e) : ℝ) =
      ((m + (e + f)).choose m : ℝ) * ((e + f).choose e : ℝ) := by
  have h := Nat.choose_mul (n := m + e + f) (k := m + e) (s := m) (by omega)
  rw [show m + e + f - m = e + f by omega, show m + e - m = e by omega] at h
  rw [show m + (e + f) = m + e + f by ring]
  exact_mod_cast (by rw [mul_comm]; exact h)

lemma X7_comp_term {η : ℝ} (hη : 1 / 2 < η) (hη1 : η ≤ 1) (m n e f : ℕ) :
    X7_Bc ((1 - η) / η) m e * X7_Bc ((1 - η) / η) n e *
      (X7_Bc η (m + e) f * X7_Bc η (n + e) f) =
    Real.sqrt ((m + (e + f)).choose m : ℝ) * Real.sqrt ((n + (e + f)).choose n : ℝ) *
      Real.sqrt (1 - η) ^ (m + n) *
      (((2 * η - 1) ^ e * (1 - η) ^ f) * ((e + f).choose e : ℝ)) := by
  have hη0 : 0 < η := by linarith
  set t := (1 - η) / η with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hη0.le
  have h1t : 0 ≤ 1 - t := by
    rw [ht, sub_nonneg, div_le_one hη0]; linarith
  have hag : Real.sqrt t * Real.sqrt η = Real.sqrt (1 - η) := by
    rw [← Real.sqrt_mul ht0, ht, div_mul_cancel₀ _ hη0.ne']
  have hb2 : Real.sqrt (1 - t) ^ 2 = 1 - t := Real.sq_sqrt h1t
  have hg2 : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη0.le
  have hd2 : Real.sqrt (1 - η) ^ 2 = 1 - η := Real.sq_sqrt (by linarith)
  have hbg : (1 - t) * η = 2 * η - 1 := by rw [ht]; field_simp; ring
  have hsC : ∀ m : ℕ, Real.sqrt ((m + e).choose m : ℝ) * Real.sqrt ((m + e + f).choose (m + e) : ℝ) =
      Real.sqrt ((m + (e + f)).choose m : ℝ) * Real.sqrt ((e + f).choose e : ℝ) := by
    intro m
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), X7_choose_id]
  have hce : Real.sqrt ((e + f).choose e : ℝ) ^ 2 = ((e + f).choose e : ℝ) :=
    Real.sq_sqrt (by positivity)
  unfold X7_Bc
  rw [show m + e + f = m + e + f from rfl]
  have key : ∀ (A B C D α β γ δ : ℝ),
      A * α ^ m * β ^ e * (B * α ^ n * β ^ e) * (C * γ ^ (m + e) * δ ^ f * (D * γ ^ (n + e) * δ ^ f))
      = (A * C) * (B * D) * (α * γ) ^ (m + n) * ((β ^ 2 * γ ^ 2) ^ e * (δ ^ 2) ^ f) := by
    intros; ring
  rw [key, hsC m, hsC n, hag, hb2, hg2, hd2, ← hbg]
  have : ∀ (P Q R W Z : ℝ), P * R * (Q * R) * W * Z = P * Q * W * (Z * R ^ 2) := by intros; ring
  rw [this, hce]

lemma X7_comp_sum {η : ℝ} (hη : 1 / 2 < η) (hη1 : η ≤ 1) (m n s : ℕ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal s, X7_Bc ((1 - η) / η) m x.1 * X7_Bc ((1 - η) / η) n x.1 *
      (X7_Bc η (m + x.1) x.2 * X7_Bc η (n + x.1) x.2) = X7_Bc η s m * X7_Bc η s n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun e f => X7_Bc ((1 - η) / η) m e * X7_Bc ((1 - η) / η) n e *
      (X7_Bc η (m + e) f * X7_Bc η (n + e) f))]
  have hterm : ∀ e ∈ Finset.range s.succ,
      X7_Bc ((1 - η) / η) m e * X7_Bc ((1 - η) / η) n e *
        (X7_Bc η (m + e) (s - e) * X7_Bc η (n + e) (s - e)) =
      Real.sqrt ((m + s).choose m : ℝ) * Real.sqrt ((n + s).choose n : ℝ) *
        Real.sqrt (1 - η) ^ (m + n) *
        ((2 * η - 1) ^ e * (1 - η) ^ (s - e) * (s.choose e : ℝ)) := by
    intro e he
    have hes : e + (s - e) = s := by have := Finset.mem_range.1 he; omega
    rw [X7_comp_term hη hη1, hes]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow]
  rw [show 2 * η - 1 + (1 - η) = η by ring]
  unfold X7_Bc
  have hg2 : η ^ s = Real.sqrt η ^ s * Real.sqrt η ^ s := by
    rw [← mul_pow, Real.mul_self_sqrt (by linarith)]
  have c1 : (s + m).choose s = (m + s).choose m := by rw [add_comm s m, Nat.choose_symm_add]
  have c2 : (s + n).choose s = (n + s).choose n := by rw [add_comm s n, Nat.choose_symm_add]
  rw [c1, c2, hg2]
  ring


section dens
attribute [local instance] Classical.propDecidable
variable {I : Type} {X : Matrix I I ℂ}

lemma X7_diag (hX : IsDensity X) (i : I) : X i i = ((X i i).re : ℂ) ∧ 0 ≤ (X i i).re := by
  obtain ⟨h1, h2⟩ := hX.2.1 {i} (fun _ => 1)
  simp at h1 h2
  exact ⟨Complex.ext (by simp) (by simp [h1]), h2⟩

lemma X7_herm (hX : IsDensity X) {i j : I} (hij : i ≠ j) : X j i = star (X i j) := by
  have hz1 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)).1
  have hz2 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)).1
  simp [Finset.sum_pair hij, hij, Ne.symm hij] at hz1 hz2
  have di := (X7_diag hX i).1
  have dj := (X7_diag hX j).1
  have hi : (X i i).im = 0 := by rw [di]; simp
  have hj : (X j j).im = 0 := by rw [dj]; simp
  apply Complex.ext
  · simp; linarith
  · simp; linarith

lemma X7_offdiag (hX : IsDensity X) (i j : I) : ‖X i j‖ ≤ ((X i i).re + (X j j).re) / 2 := by
  obtain ⟨di, di0⟩ := X7_diag hX i
  obtain ⟨dj, dj0⟩ := X7_diag hX j
  by_cases hij : i = j
  · subst hij
    conv_lhs => rw [di]
    rw [Complex.norm_real, Real.norm_of_nonneg di0]; linarith
  set w := X i j with hw
  by_cases hw0 : w = 0
  · rw [hw0, norm_zero]; linarith
  have hn : (0:ℝ) < ‖w‖ := norm_pos_iff.2 hw0
  set c : ℂ := -(star w) / (‖w‖ : ℂ) with hc
  have hnc : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hww : w * star w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hwc : w * c = -(‖w‖ : ℂ) := by
    rw [hc, mul_div_assoc', mul_neg, hww]; push_cast; field_simp
  have hcw : star c * star w = -(‖w‖ : ℂ) := by
    rw [← star_mul', mul_comm, hwc]; simp [Complex.star_def, Complex.conj_ofReal]
  have hcc : star c * c = 1 := by
    rw [hc]
    have : star (-(star w) / (‖w‖ : ℂ)) = -w / (‖w‖ : ℂ) := by
      simp [Complex.star_def, Complex.conj_ofReal, map_div₀]
    rw [this]
    field_simp
    rw [hww]; push_cast; ring
  have h2 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then c else 0)).2
  simp only [Finset.sum_pair hij, if_pos, if_neg (Ne.symm hij), if_neg hij, star_one, one_mul,
    mul_one, if_true] at h2
  rw [X7_herm hX hij, ← hw] at h2
  have hform : X i i + w * c + (star c * star w + star c * X j j * c) =
      ((X i i).re + (X j j).re - 2 * ‖w‖ : ℝ) := by
    rw [di, dj] at *
    push_cast
    linear_combination hwc + hcw + ((X j j).re : ℂ) * hcc
  rw [hform, Complex.ofReal_re] at h2
  linarith

end dens

lemma X7_ι_apply (k : ℕ) (i : Fin 1) : X7_ι k i = k := rfl


lemma X7_main {η : ℝ} (hη : 1 / 2 < η) (hη1 : η ≤ 1) (X : FockKernel 1) (hX : IsDensity X)
    (a b : NumberString 1) :
    pureLoss 1 ((1 - η) / η) (pureLoss 1 η X) a b = charlieMarginal (broadcast 1 η X) a b := by
  rw [X7_bob, X7_eve]
  simp only [X7_bob, X7_ι_apply]
  set m := a 0
  set n := b 0
  set t := (1 - η) / η
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
  let c : ℕ × ℕ → ℝ := fun p => X7_Bc t m p.1 * X7_Bc t n p.1 *
    (X7_Bc η (m + p.1) p.2 * X7_Bc η (n + p.1) p.2)
  have hc0 : ∀ p, 0 ≤ c p := fun p => by
    simp only [c]
    have := X7_Bc_nonneg t m p.1; have := X7_Bc_nonneg t n p.1
    have := X7_Bc_nonneg η (m + p.1) p.2; have := X7_Bc_nonneg η (n + p.1) p.2
    positivity
  let F : ℕ × ℕ → ℂ := fun p => (c p : ℂ) * X (X7_ι (m + (p.1 + p.2))) (X7_ι (n + (p.1 + p.2)))
  let D : ℕ → ℝ := fun k => (X (X7_ι k) (X7_ι k)).re
  have hD0 : ∀ k, 0 ≤ D k := fun k => (X7_diag hX _).2
  have hDs : Summable D := by
    have h := hX.2.2.1
    rw [← (Equiv.funUnique (Fin 1) ℕ).symm.summable_iff] at h
    have e : ∀ k, (Equiv.funUnique (Fin 1) ℕ).symm k = X7_ι k := by
      intro k; funext i; simp [X7_ι]
    simp only [Function.comp_def, e] at h
    exact h
  let G : ℕ × ℕ → ℝ := fun p => c p * ((D (m + (p.1 + p.2)) + D (n + (p.1 + p.2))) / 2)
  have hFG : ∀ p, ‖F p‖ ≤ G p := by
    intro p
    simp only [F, G, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 p)]
    exact mul_le_mul_of_nonneg_left (X7_offdiag hX _ _) (hc0 p)
  have hcs : ∀ s, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal s, c x = X7_Bc η s m * X7_Bc η s n :=
    fun s => X7_comp_sum hη hη1 m n s
  have hGs : Summable G := by
    rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
    rw [summable_sigma_of_nonneg (fun x => by
      simp only [Function.comp_apply, G]
      exact mul_nonneg (hc0 _) (by have := hD0 (m + ((x.2 : ℕ × ℕ).1 + (x.2 : ℕ × ℕ).2))
                                   have := hD0 (n + ((x.2 : ℕ × ℕ).1 + (x.2 : ℕ × ℕ).2))
                                   positivity))]
    refine ⟨fun s => Summable.of_finite, ?_⟩
    have hfib : ∀ s, (∑' y : Finset.HasAntidiagonal.antidiagonal s,
        (G ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨s, y⟩) =
        X7_Bc η s m * X7_Bc η s n * ((D (m + s) + D (n + s)) / 2) := by
      intro s
      simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
      rw [Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal s)
        (fun x => G x)]
      rw [← hcs, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      simp only [G, hx]
    simp only [hfib]
    have hsum0 := (((summable_nat_add_iff m).2 hDs).add ((summable_nat_add_iff n).2 hDs)).div_const 2
    have hsum : Summable (fun s => (D (m + s) + D (n + s)) / 2) :=
      hsum0.congr (fun s => by rw [add_comm s m, add_comm s n])
    refine Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) hsum
    · have := X7_Bc_nonneg η s m; have := X7_Bc_nonneg η s n
      have := hD0 (m + s); have := hD0 (n + s); positivity
    · have h1 := X7_Bc_le_one (by linarith : (0:ℝ) ≤ η) hη1 s m
      have h2 := X7_Bc_le_one (by linarith : (0:ℝ) ≤ η) hη1 s n
      have := X7_Bc_nonneg η s m; have := X7_Bc_nonneg η s n
      have := hD0 (m + s); have := hD0 (n + s)
      have hp : X7_Bc η s m * X7_Bc η s n ≤ 1 := by nlinarith
      have hq : 0 ≤ (D (m + s) + D (n + s)) / 2 := by positivity
      exact mul_le_of_le_one_left hq hp
  have hFs : Summable F := Summable.of_norm_bounded hGs hFG
  have step1 : (∑' e : ℕ, ((X7_Bc t m e * X7_Bc t n e : ℝ) : ℂ) *
      ∑' f : ℕ, ((X7_Bc η (m + e) f * X7_Bc η (n + e) f : ℝ) : ℂ) *
        X (X7_ι (m + e + f)) (X7_ι (n + e + f))) = ∑' e : ℕ, ∑' f : ℕ, F (e, f) := by
    apply tsum_congr; intro e
    rw [← tsum_mul_left]
    apply tsum_congr; intro f
    simp only [F, c, add_assoc]
    push_cast; ring
  rw [step1, ← hFs.tsum_prod' (fun e => hFs.prod_factor e)]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq]
  have hFs' := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff (f := F)).2 hFs
  refine Eq.trans (hFs'.tsum_sigma' (fun s => Summable.of_finite)) ?_
  apply tsum_congr; intro s
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal s) F]
  have : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal s, F x =
      (c x : ℂ) * X (X7_ι (m + s)) (X7_ι (n + s)) := by
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    simp only [F, hx]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← Complex.ofReal_sum, hcs, add_comm s m,
    add_comm s n]

end X7L3DG

noncomputable section

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support50.P06 in
theorem solution (eta : ℝ) (heta : 1 / 2 < eta) (heta_one : eta ≤ 1)
    (rho : State (NumberString 1)) :
    pureLoss 1 ((1 - eta) / eta) (pureLoss 1 eta rho.coefficients) =
      (charlieMarginal (broadcast 1 eta rho.coefficients)) := by
  funext a b
  exact X7L3DG.X7_main heta heta_one rho.coefficients rho.density a b
