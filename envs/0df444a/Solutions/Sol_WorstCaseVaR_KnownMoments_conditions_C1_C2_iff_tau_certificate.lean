-- Prove2me | solution 1 for WorstCaseVaR.KnownMoments.conditions_C1_C2_iff_tau_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:07:18.736633+00:00
-- url     : https://prove2.me/submissions/6dae6200-a953-4ad0-9467-223d0a4ecbf6

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

set_option autoImplicit false

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace SLemma969718ea

theorem key_ineq {V : Type*} [AddCommGroup V] [Module ℝ V] (f g : V → ℝ)
    (hf : ∀ u v : V, ∃ c : ℝ, ∀ s : ℝ, f (u + s • v) = f u + s * c + s ^ 2 * f v)
    (hg : ∀ u v : V, ∃ c : ℝ, ∀ s : ℝ, g (u + s • v) = g u + s * c + s ^ 2 * g v)
    (hfg : ∀ z, g z = 0 → 0 ≤ f z) (z1 z2 : V) (h1 : 0 < g z1) (h2 : g z2 < 0) :
    0 ≤ f z1 * (-g z2) + f z2 * g z1 := by
  obtain ⟨cf, hcf⟩ := hf z1 z2
  obtain ⟨cg, hcg⟩ := hg z1 z2
  have hDpos : 0 < cg ^ 2 - 4 * g z1 * g z2 := by nlinarith [sq_nonneg cg, mul_pos h1 (neg_pos.mpr h2)]
  obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 ≤ r ∧ r ^ 2 = cg ^ 2 - 4 * g z1 * g z2 :=
    ⟨Real.sqrt _, Real.sqrt_nonneg _, Real.sq_sqrt hDpos.le⟩
  have hrcg : cg < r := by nlinarith [mul_pos h1 (neg_pos.mpr h2)]
  have hrcg' : -cg < r := by nlinarith [mul_pos h1 (neg_pos.mpr h2)]
  have hg2 : 0 < -2 * g z2 := by linarith
  -- the two roots
  have root : ∀ s : ℝ, s * (-2 * g z2) = cg + r ∨ s * (-2 * g z2) = cg - r →
      g z1 + s * cg + s ^ 2 * g z2 = 0 := by
    intro s hs
    have h4 : 4 * g z2 * (g z1 + s * cg + s ^ 2 * g z2) = 0 := by
      rcases hs with hs | hs
      · linear_combination (s * (-2 * g z2) - cg + r) * hs + hr2
      · linear_combination (s * (-2 * g z2) - cg - r) * hs + hr2
    have : (4 * g z2) ≠ 0 := by intro h; linarith
    exact (mul_eq_zero.mp h4).resolve_left this
  have phi : ∀ s : ℝ, g z1 + s * cg + s ^ 2 * g z2 = 0 →
      0 ≤ f z1 * (-g z2) + f z2 * g z1 + s * (cf * (-g z2) + f z2 * cg) := by
    intro s hs
    have h0 : g (z1 + s • z2) = 0 := by rw [hcg]; exact hs
    have hf0 := hfg _ h0
    rw [hcf] at hf0
    have := mul_nonneg hf0 (neg_nonneg.mpr h2.le)
    have e : f z1 * (-g z2) + f z2 * g z1 + s * (cf * (-g z2) + f z2 * cg)
        = (f z1 + s * cf + s ^ 2 * f z2) * -g z2 := by linear_combination (f z2) * hs
    rw [e]; exact this
  set s1 := (cg + r) / (-2 * g z2) with hs1d
  set s2 := (cg - r) / (-2 * g z2) with hs2d
  have e1 : s1 * (-2 * g z2) = cg + r := div_mul_cancel₀ _ hg2.ne'
  have e2 : s2 * (-2 * g z2) = cg - r := div_mul_cancel₀ _ hg2.ne'
  have hs1 : 0 < s1 := div_pos (by linarith) hg2
  have hs2 : s2 < 0 := div_neg_of_neg_of_pos (by linarith) hg2
  have p1 := phi s1 (root s1 (Or.inl e1))
  have p2 := phi s2 (root s2 (Or.inr e2))
  set A := f z1 * (-g z2) + f z2 * g z1
  set B := cf * (-g z2) + f z2 * cg
  have : 0 ≤ A * (s1 - s2) := by
    have := mul_nonneg hs1.le p2
    have := mul_nonneg (neg_nonneg.mpr hs2.le) p1
    nlinarith
  by_contra hA
  push Not at hA
  nlinarith [mul_neg_of_neg_of_pos hA (show 0 < s1 - s2 by linarith)]

theorem s_lemma {V : Type*} [AddCommGroup V] [Module ℝ V] (f g : V → ℝ)
    (hf : ∀ u v : V, ∃ c : ℝ, ∀ s : ℝ, f (u + s • v) = f u + s * c + s ^ 2 * f v)
    (hg : ∀ u v : V, ∃ c : ℝ, ∀ s : ℝ, g (u + s • v) = g u + s * c + s ^ 2 * g v)
    (hfg : ∀ z, g z ≤ 0 → 0 ≤ f z) (hslater : ∃ z0, g z0 < 0) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ z, 0 ≤ f z + τ * g z := by
  obtain ⟨z0, hz0⟩ := hslater
  let B : Set ℝ := {b | ∃ z, g z < 0 ∧ b = f z / (-g z)}
  have hlow : ∀ b ∈ B, 0 ≤ b := by
    rintro b ⟨z, hz, rfl⟩; exact div_nonneg (hfg z hz.le) (by linarith)
  have hBne : B.Nonempty := ⟨_, z0, hz0, rfl⟩
  have hBbdd : BddBelow B := ⟨0, hlow⟩
  refine ⟨sInf B, le_csInf hBne hlow, ?_⟩
  intro z
  rcases lt_trichotomy (g z) 0 with h | h | h
  · have : sInf B ≤ f z / (-g z) := csInf_le hBbdd ⟨z, h, rfl⟩
    rw [le_div_iff₀ (by linarith)] at this; linarith
  · rw [h]; simpa using hfg z h.le
  · have : -f z / g z ≤ sInf B := by
      refine le_csInf hBne ?_
      rintro b ⟨z2, hz2, rfl⟩
      rw [div_le_div_iff₀ h (by linarith)]
      have := key_ineq f g hf hg (fun z h => hfg z h.le) z z2 h hz2
      nlinarith
    rw [div_le_iff₀ h] at this; linarith

end SLemma969718ea

namespace SLemma969718ea
open WorstCaseVaR.KnownMoments

def Qf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (z : ι → ℝ) : ℝ := z ⬝ᵥ (A *ᵥ z)

def tz {n : ℕ} (z : Fin n ⊕ Fin 1 → ℝ) : ℝ := z (Sum.inr 0)

def Lf {n : ℕ} (w : Fin n → ℝ) (z : Fin n ⊕ Fin 1 → ℝ) : ℝ := ∑ i, w i * z (Sum.inl i)

theorem quad_expand {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (hA : A.IsSymm) (u v : ι → ℝ)
    (s : ℝ) : Qf A (u + s • v) = Qf A u + s * (2 * (u ⬝ᵥ (A *ᵥ v))) + s ^ 2 * Qf A v := by
  have hsym : v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, dotProduct_comm]
  simp only [Qf, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, hsym]
  ring

theorem quad_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (c : ℝ) (v : ι → ℝ) :
    Qf A (c • v) = c ^ 2 * Qf A v := by
  simp only [Qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem Lf_add_smul {n : ℕ} (w : Fin n → ℝ) (u v : Fin n ⊕ Fin 1 → ℝ) (s : ℝ) :
    Lf w (u + s • v) = Lf w u + s * Lf w v := by
  simp only [Lf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

theorem Lf_smul {n : ℕ} (w : Fin n → ℝ) (c : ℝ) (v : Fin n ⊕ Fin 1 → ℝ) :
    Lf w (c • v) = c * Lf w v := by
  simp only [Lf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem bordered_form {n : ℕ} (v : Fin n → ℝ) (c : ℝ) (z : Fin n ⊕ Fin 1 → ℝ) :
    z ⬝ᵥ (bordered 0 v c *ᵥ z) = 2 * tz z * Lf v z + c * tz z ^ 2 := by
  simp only [bordered, dotProduct, mulVec, Fintype.sum_sum_type, tz, Lf]
  simp
  have h : ∑ x, z (Sum.inl x) * (v x * z (Sum.inr 0))
      = z (Sum.inr 0) * ∑ x, v x * z (Sum.inl x) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]; ring

theorem bordered_symm {n : ℕ} (v : Fin n → ℝ) (c : ℝ) : (bordered 0 v c).IsSymm := by
  unfold bordered
  exact IsSymm.fromBlocks isSymm_zero (by ext i j; rfl) (IsSymm.ext fun _ _ => rfl)

end SLemma969718ea

open WorstCaseVaR.KnownMoments InnerProductSpace in
theorem solution {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (hM : M.IsSymm)
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0) (γ : ℝ) :
    ((∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ quadFn M ⇑x) ∧
        (∀ x : EuclideanSpace ℝ (Fin n), γ + ⟪x, w⟫_ℝ ≤ 0 → 1 ≤ quadFn M ⇑x)) ↔
      ∃ τ : ℝ, 0 ≤ τ ∧ M.PosSemidef ∧
        (M + bordered 0 (τ • ⇑w) (-1 + 2 * τ * γ)).PosSemidef := by
  classical
  have hquad : ∀ x : EuclideanSpace ℝ (Fin n), quadFn M ⇑x = SLemma969718ea.Qf M (liftVec ⇑x) := fun x => rfl
  have hL_lift : ∀ x : EuclideanSpace ℝ (Fin n), SLemma969718ea.Lf (⇑w) (liftVec ⇑x) = ⟪x, w⟫_ℝ := by
    intro x
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [SLemma969718ea.Lf, liftVec, dotProduct]
  have ht_lift : ∀ v : Fin n → ℝ, SLemma969718ea.tz (liftVec v) = 1 := fun v => rfl
  have hBd : ∀ (τ : ℝ) (z : Fin n ⊕ Fin 1 → ℝ),
      z ⬝ᵥ (bordered 0 (τ • ⇑w) (-1 + 2 * τ * γ) *ᵥ z)
        = 2 * τ * SLemma969718ea.tz z * (SLemma969718ea.Lf (⇑w) z + γ * SLemma969718ea.tz z) - SLemma969718ea.tz z ^ 2 := by
    intro τ z
    rw [SLemma969718ea.bordered_form]
    have : SLemma969718ea.Lf (τ • ⇑w) z = τ * SLemma969718ea.Lf (⇑w) z := by
      simp only [SLemma969718ea.Lf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [this]; ring
  -- decomposition of a vector with nonzero last coordinate
  have hdecomp : ∀ z : Fin n ⊕ Fin 1 → ℝ, SLemma969718ea.tz z ≠ 0 →
      z = SLemma969718ea.tz z • liftVec ⇑(WithLp.toLp 2 (fun i => z (Sum.inl i) / SLemma969718ea.tz z) :
        EuclideanSpace ℝ (Fin n)) := by
    intro z ht
    funext j
    rcases j with i | j
    · simp [liftVec]; field_simp
    · fin_cases j; simp [liftVec, SLemma969718ea.tz]
  constructor
  · rintro ⟨h1, h2⟩
    have hpsd : ∀ z, 0 ≤ SLemma969718ea.Qf M z := by
      intro z
      by_cases ht : SLemma969718ea.tz z = 0
      · let e : Fin n ⊕ Fin 1 → ℝ := liftVec 0
        have hs : ∀ s : ℝ, 0 ≤ SLemma969718ea.Qf M e + s * (2 * (e ⬝ᵥ (M *ᵥ z))) + s ^ 2 * SLemma969718ea.Qf M z := by
          intro s
          have he : e + s • z = liftVec ⇑(WithLp.toLp 2 (fun i => s * z (Sum.inl i)) :
              EuclideanSpace ℝ (Fin n)) := by
            funext j
            rcases j with i | j
            · simp [e, liftVec]
            · fin_cases j; simp [e, liftVec, SLemma969718ea.tz] at ht ⊢; simp [ht]
          have h := h1 (WithLp.toLp 2 (fun i => s * z (Sum.inl i)))
          rw [hquad, ← he, SLemma969718ea.quad_expand M hM] at h
          exact h
        have d := discrim_le_zero (a := SLemma969718ea.Qf M z) (b := 2 * (e ⬝ᵥ (M *ᵥ z))) (c := SLemma969718ea.Qf M e)
          (fun x => by have := hs x; nlinarith)
        unfold discrim at d
        have h0 := hs 0
        have h1' := hs 1
        by_contra hneg
        push Not at hneg
        generalize SLemma969718ea.Qf M z = a at *
        generalize SLemma969718ea.Qf M e = c at *
        generalize 2 * (e ⬝ᵥ (M *ᵥ z)) = b at *
        have hc : 0 ≤ c := by linarith
        have hac : a * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le hc
        have hb : b ^ 2 ≤ 0 := by linarith
        have hb0 : b = 0 := by nlinarith [sq_nonneg b]
        have hac0 : a * c = 0 := by nlinarith [sq_nonneg b]
        have hc0 : c = 0 := (mul_eq_zero.mp hac0).resolve_left hneg.ne
        subst hb0 hc0
        linarith
      · rw [hdecomp z ht, SLemma969718ea.quad_smul, ← hquad]
        exact mul_nonneg (sq_nonneg _) (h1 _)
    have hMpsd : M.PosSemidef :=
      PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_iff_isSymm.mpr hM)
        (fun z => by simpa [SLemma969718ea.Qf] using hpsd z)
    let f : (Fin n ⊕ Fin 1 → ℝ) → ℝ := fun z => SLemma969718ea.Qf M z - SLemma969718ea.tz z ^ 2
    let g : (Fin n ⊕ Fin 1 → ℝ) → ℝ := fun z => SLemma969718ea.tz z * (SLemma969718ea.Lf (⇑w) z + γ * SLemma969718ea.tz z)
    have htz : ∀ (u v : Fin n ⊕ Fin 1 → ℝ) (s : ℝ), SLemma969718ea.tz (u + s • v) = SLemma969718ea.tz u + s * SLemma969718ea.tz v := by
      intro u v s; simp [SLemma969718ea.tz]
    have hf : ∀ u v : Fin n ⊕ Fin 1 → ℝ, ∃ c : ℝ, ∀ s : ℝ,
        f (u + s • v) = f u + s * c + s ^ 2 * f v := by
      intro u v
      refine ⟨2 * (u ⬝ᵥ (M *ᵥ v)) - 2 * SLemma969718ea.tz u * SLemma969718ea.tz v, fun s => ?_⟩
      simp only [f, SLemma969718ea.quad_expand M hM, htz]
      ring
    have hg : ∀ u v : Fin n ⊕ Fin 1 → ℝ, ∃ c : ℝ, ∀ s : ℝ,
        g (u + s • v) = g u + s * c + s ^ 2 * g v := by
      intro u v
      refine ⟨SLemma969718ea.tz u * SLemma969718ea.Lf (⇑w) v + SLemma969718ea.tz v * SLemma969718ea.Lf (⇑w) u + 2 * γ * SLemma969718ea.tz u * SLemma969718ea.tz v, fun s => ?_⟩
      simp only [g, SLemma969718ea.Lf_add_smul, htz]
      ring
    have hfg : ∀ z, g z ≤ 0 → 0 ≤ f z := by
      intro z hz
      by_cases ht : SLemma969718ea.tz z = 0
      · simp only [f, ht]; simpa using hpsd z
      · set x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => z (Sum.inl i) / SLemma969718ea.tz z)
          with hx
        have hzx := hdecomp z ht
        rw [← hx] at hzx
        have hQ : SLemma969718ea.Qf M z = SLemma969718ea.tz z ^ 2 * quadFn M ⇑x := by
          rw [hzx, SLemma969718ea.quad_smul, hquad]; congr 1; rw [← hzx]
        have hLz : SLemma969718ea.Lf (⇑w) z = SLemma969718ea.tz z * ⟪x, w⟫_ℝ := by
          rw [hzx, SLemma969718ea.Lf_smul, hL_lift]; congr 1; rw [← hzx]
        have hgz : g z = SLemma969718ea.tz z ^ 2 * (γ + ⟪x, w⟫_ℝ) := by
          simp only [g, hLz]; ring
        have ht2 : 0 < SLemma969718ea.tz z ^ 2 := by positivity
        have hc : γ + ⟪x, w⟫_ℝ ≤ 0 := by
          by_contra hc; push Not at hc
          have := mul_pos ht2 hc; linarith
        have := h2 x hc
        simp only [f, hQ]
        nlinarith
    have hslater : ∃ z0, g z0 < 0 := by
      have hwn : 0 < ‖w‖ ^ 2 := by positivity
      refine ⟨liftVec ⇑((-(|γ| + 1) / ‖w‖ ^ 2) • w), ?_⟩
      simp only [g, ht_lift, hL_lift, real_inner_smul_left, real_inner_self_eq_norm_sq]
      rw [div_mul_cancel₀ _ hwn.ne']
      have := le_abs_self γ
      linarith
    obtain ⟨τ, hτ, hall⟩ := SLemma969718ea.s_lemma f g hf hg hfg hslater
    refine ⟨τ / 2, by linarith, hMpsd, ?_⟩
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_iff_isSymm.mpr (hM.add (SLemma969718ea.bordered_symm _ _))) fun z => ?_
    simp only [star_trivial, add_mulVec, dotProduct_add]
    rw [hBd]
    have := hall z
    simp only [f, g, SLemma969718ea.Qf] at this
    nlinarith
  · rintro ⟨τ, hτ, hMpsd, hB⟩
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := hMpsd.dotProduct_mulVec_nonneg (liftVec ⇑x)
      simpa [quadFn] using this
    · have := hB.dotProduct_mulVec_nonneg (liftVec ⇑x)
      simp only [star_trivial, add_mulVec, dotProduct_add] at this
      rw [hBd, ht_lift, hL_lift] at this
      rw [hquad]
      simp only [SLemma969718ea.Qf]
      nlinarith
