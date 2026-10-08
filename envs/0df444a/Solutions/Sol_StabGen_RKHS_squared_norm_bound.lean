-- Prove2me | solution 1 for StabGen.RKHS.squared_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:33:29.102482+00:00
-- url     : https://prove2.me/submissions/0599d933-6092-419b-9947-ac5cb89e027f

import Mathlib
import Definitions.Def_StabGen_RKHS_Regularization
import Definitions.Def_FoundationsML_Stability_IsRKHSOf

set_option autoImplicit false

/- Proof of Theorem 22, p. 515: the squared RKHS norm bound for the
minimizers of equations (19) and (20). -/
open StabGen.RKHS FoundationsML.Stability in
theorem solution {X Y H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {m : ℕ}
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ)
    (c : ℝ → Y → ℝ) (σ lam : ℝ) (S : Fin m → X × Y)
    (i : Fin m) (f f' : H)
    (hRKHS : IsRKHSOf K Φ ev)
    (hσ : SigmaAdmissible (Set.range ev) c σ) (hlam : 0 < lam)
    (hmin : ∀ g : H, regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) f ≤
      regRisk c ev S lam (fun h : H => ‖h‖ ^ 2) g)
    (hmin' : ∀ g : H, truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) f' ≤
      truncRegRisk c ev S i lam (fun h : H => ‖h‖ ^ 2) g) :
    2 * ‖f' - f‖ ^ 2 ≤ (σ / (lam * (m : ℝ))) * |ev (f' - f) (S i).1| := by
  obtain ⟨-, hev⟩ := hRKHS
  obtain ⟨hσ0, hconv, hlip⟩ := hσ
  have hM : (0:ℝ) < (m : ℝ) := by
    have : 0 < m := Fin.pos i
    exact_mod_cast this
  have evadd : ∀ (g h : H) (x : X), ev (g + h) x = ev g x + ev h x := by
    intro g h x; rw [hev, hev, hev, inner_add_left]
  have evsub : ∀ (g h : H) (x : X), ev (g - h) x = ev g x - ev h x := by
    intro g h x; rw [hev, hev, hev, inner_sub_left]
  have evsmul : ∀ (s : ℝ) (g : H) (x : X), ev (s • g) x = s * ev g x := by
    intro s g x; rw [hev, hev, real_inner_smul_left]
  -- the key inequality at every step size t ∈ (0, 1]
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      lam * (2 * t * (1 - t) * ‖f' - f‖ ^ 2) ≤
        1 / (m : ℝ) * (σ * (t * |ev f' (S i).1 - ev f (S i).1|)) := by
    intro t ht0 ht1
    have h1t : (0:ℝ) ≤ 1 - t := by linarith
    have hnorm : ‖f‖ ^ 2 - ‖f + t • (f' - f)‖ ^ 2 + ‖f'‖ ^ 2 - ‖f' - t • (f' - f)‖ ^ 2
        = 2 * t * (1 - t) * ‖f' - f‖ ^ 2 := by
      have hgen : ∀ d : H, ‖f‖ ^ 2 - ‖f + t • d‖ ^ 2 + ‖f + d‖ ^ 2 - ‖f + (1 - t) • d‖ ^ 2
          = 2 * t * (1 - t) * ‖d‖ ^ 2 := by
        intro d
        rw [norm_add_sq_real, norm_add_sq_real, norm_add_sq_real, norm_smul, norm_smul,
          real_inner_smul_right, real_inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs,
          Real.norm_eq_abs, sq_abs, sq_abs]
        ring
      have e2 : f' - t • (f' - f) = f + (1 - t) • (f' - f) := by module
      have := hgen (f' - f)
      rwa [show f + (f' - f) = f' by abel, ← e2] at this
    have h1 := hmin (f + t • (f' - f))
    have h2 := hmin' (f' - t • (f' - f))
    simp only [regRisk, truncRegRisk, EmpiricalError, Loss, evadd, evsub, evsmul] at h1 h2
    simp only [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h1
    have hc : ∀ y : Y, ∀ a b : ℝ,
        c (a + t * (b - a)) y + c (b - t * (b - a)) y ≤ c a y + c b y := by
      intro y a b
      have e1 := (hconv y).2 (Set.mem_univ a) (Set.mem_univ b) h1t ht0.le (by ring)
      have e2 := (hconv y).2 (Set.mem_univ a) (Set.mem_univ b) ht0.le h1t (by ring)
      simp only [smul_eq_mul] at e1 e2
      have q1 : a + t * (b - a) = (1 - t) * a + t * b := by ring
      have q2 : b - t * (b - a) = t * a + (1 - t) * b := by ring
      rw [q1, q2]
      nlinarith [e1, e2]
    have hT : ∑ j ∈ Finset.univ.erase i,
        (c (ev f (S j).1 + t * (ev f' (S j).1 - ev f (S j).1)) (S j).2 +
          c (ev f' (S j).1 - t * (ev f' (S j).1 - ev f (S j).1)) (S j).2) ≤
        ∑ j ∈ Finset.univ.erase i, (c (ev f (S j).1) (S j).2 + c (ev f' (S j).1) (S j).2) :=
      Finset.sum_le_sum fun j _ => hc _ _ _
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hT
    have hL : c (ev f (S i).1 + t * (ev f' (S i).1 - ev f (S i).1)) (S i).2 -
        c (ev f (S i).1) (S i).2 ≤ σ * (t * |ev f' (S i).1 - ev f (S i).1|) := by
      have hd1 : ev f (S i).1 + t * (ev f' (S i).1 - ev f (S i).1) ∈
          predictionDomain (Set.range ev) :=
        ⟨ev (f + t • (f' - f)), ⟨_, rfl⟩, (S i).1, by rw [evadd, evsmul, evsub]⟩
      have hd2 : ev f (S i).1 ∈ predictionDomain (Set.range ev) :=
        ⟨ev f, ⟨_, rfl⟩, (S i).1, rfl⟩
      have := hlip _ hd1 _ hd2 (S i).2
      have e : |ev f (S i).1 + t * (ev f' (S i).1 - ev f (S i).1) - ev f (S i).1| =
          t * |ev f' (S i).1 - ev f (S i).1| := by
        rw [show ev f (S i).1 + t * (ev f' (S i).1 - ev f (S i).1) - ev f (S i).1 =
            t * (ev f' (S i).1 - ev f (S i).1) by ring, abs_mul, abs_of_nonneg ht0.le]
      rw [e] at this
      exact (le_abs_self _).trans this
    have hw : (0:ℝ) ≤ 1 / (m : ℝ) := by positivity
    have hT' := mul_le_mul_of_nonneg_left hT hw
    have hL' := mul_le_mul_of_nonneg_left hL hw
    rw [← hnorm]
    nlinarith [h1, h2, hT', hL']
  rw [evsub]
  set A := ‖f' - f‖ ^ 2 with hA
  set D := |ev f' (S i).1 - ev f (S i).1| with hD
  set R := σ / (lam * (m : ℝ)) * D with hR
  have hA0 : 0 ≤ A := by positivity
  have hD0 : 0 ≤ D := abs_nonneg _
  have hR0 : 0 ≤ R := by positivity
  have hk : ∀ t : ℝ, 0 < t → t ≤ 1 → 2 * (1 - t) * A ≤ R := by
    intro t ht0 ht1
    have h := key t ht0 ht1
    have hlt : 0 < lam * t := mul_pos hlam ht0
    have eqR : R * (lam * t) = 1 / (m : ℝ) * (σ * (t * D)) := by
      rw [hR]; field_simp
    have : 2 * (1 - t) * A * (lam * t) ≤ R * (lam * t) := by
      rw [eqR]; nlinarith [h]
    exact le_of_mul_le_mul_right this hlt
  by_contra hcon0
  have hcon := not_le.mp hcon0
  have hApos : 0 < A := by linarith
  set t := (2 * A - R) / (4 * A) with ht
  have htA : t * (4 * A) = 2 * A - R := by
    rw [ht]; field_simp
  have ht0 : 0 < t := by
    rw [ht]; apply div_pos <;> linarith
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by linarith)]; linarith
  have := hk t ht0 ht1
  nlinarith [this, htA]
