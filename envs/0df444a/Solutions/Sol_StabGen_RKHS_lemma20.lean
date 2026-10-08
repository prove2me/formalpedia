-- Prove2me | solution 1 for StabGen.RKHS.lemma20
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:29:08.242853+00:00
-- url     : https://prove2.me/submissions/d8abb63a-dd30-4973-8321-416455682c2f

import Mathlib
import Definitions.Def_StabGen_RKHS_Regularization

set_option autoImplicit false

open StabGen.RKHS in
theorem solution {X Y : Type*} {m : ℕ} (F : Set (X → ℝ))
    (c : ℝ → Y → ℝ) (σ lam : ℝ) (N : (X → ℝ) → ℝ)
    (S : Fin m → X × Y) (i : Fin m) (f f' : X → ℝ)
    (hF : Convex ℝ F) (hN : ∀ g ∈ F, 0 ≤ N g)
    (hσ : SigmaAdmissible F c σ) (hlam : 0 < lam)
    (hf : f ∈ F) (hf' : f' ∈ F)
    (hmin : ∀ g ∈ F, regRisk c (id : (X → ℝ) → X → ℝ) S lam N f ≤
      regRisk c (id : (X → ℝ) → X → ℝ) S lam N g)
    (hmin' : ∀ g ∈ F, truncRegRisk c (id : (X → ℝ) → X → ℝ) S i lam N f' ≤
      truncRegRisk c (id : (X → ℝ) → X → ℝ) S i lam N g)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    N f - N (f + t • (f' - f)) + N f' - N (f' - t • (f' - f)) ≤
      (t * σ / (lam * (m : ℝ))) * |f' (S i).1 - f (S i).1| := by
  obtain ⟨hσ0, hconv, hlip⟩ := hσ
  have h1t : (0:ℝ) ≤ 1 - t := by linarith
  have hg1 : f + t • (f' - f) ∈ F := by
    have h := hF hf hf' h1t ht0 (by ring)
    convert h using 1
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hg2 : f' - t • (f' - f) ∈ F := by
    have h := hF hf hf' ht0 h1t (by ring)
    convert h using 1
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have h1 := hmin _ hg1
  have h2 := hmin' _ hg2
  simp only [regRisk, truncRegRisk, FoundationsML.Stability.EmpiricalError,
    FoundationsML.Stability.Loss, id, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul] at h1 h2
  simp only [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h1
  have hc : ∀ y : Y, ∀ a b : ℝ,
      c (a + t * (b - a)) y + c (b - t * (b - a)) y ≤ c a y + c b y := by
    intro y a b
    have e1 := (hconv y).2 (Set.mem_univ a) (Set.mem_univ b) h1t ht0 (by ring)
    have e2 := (hconv y).2 (Set.mem_univ a) (Set.mem_univ b) ht0 h1t (by ring)
    simp only [smul_eq_mul] at e1 e2
    have q1 : a + t * (b - a) = (1 - t) * a + t * b := by ring
    have q2 : b - t * (b - a) = t * a + (1 - t) * b := by ring
    rw [q1, q2]
    nlinarith [e1, e2]
  have hT : ∑ j ∈ Finset.univ.erase i,
      (c (f (S j).1 + t * (f' (S j).1 - f (S j).1)) (S j).2 +
        c (f' (S j).1 - t * (f' (S j).1 - f (S j).1)) (S j).2) ≤
      ∑ j ∈ Finset.univ.erase i, (c (f (S j).1) (S j).2 + c (f' (S j).1) (S j).2) :=
    Finset.sum_le_sum fun j _ => hc _ _ _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hT
  have hL : c (f (S i).1 + t * (f' (S i).1 - f (S i).1)) (S i).2 - c (f (S i).1) (S i).2 ≤
      σ * (t * |f' (S i).1 - f (S i).1|) := by
    have hd1 : f (S i).1 + t * (f' (S i).1 - f (S i).1) ∈ predictionDomain F :=
      ⟨f + t • (f' - f), hg1, (S i).1, by
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]⟩
    have hd2 : f (S i).1 ∈ predictionDomain F := ⟨f, hf, (S i).1, rfl⟩
    have := hlip _ hd1 _ hd2 (S i).2
    have e : |f (S i).1 + t * (f' (S i).1 - f (S i).1) - f (S i).1| =
        t * |f' (S i).1 - f (S i).1| := by
      rw [show f (S i).1 + t * (f' (S i).1 - f (S i).1) - f (S i).1 =
          t * (f' (S i).1 - f (S i).1) by ring, abs_mul, abs_of_nonneg ht0]
    rw [e] at this
    exact (le_abs_self _).trans this
  have hM : (0:ℝ) < (m : ℝ) := by
    have : 0 < m := Fin.pos i
    exact_mod_cast this
  have hw : (0:ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hT' := mul_le_mul_of_nonneg_left hT hw
  have hL' := mul_le_mul_of_nonneg_left hL hw
  have key : lam * (N f - N (f + t • (f' - f)) + N f' - N (f' - t • (f' - f))) ≤
      1 / (m : ℝ) * (σ * (t * |f' (S i).1 - f (S i).1|)) := by
    nlinarith [h1, h2, hT', hL']
  have eq : t * σ / (lam * (m : ℝ)) * |f' (S i).1 - f (S i).1| =
      (1 / (m : ℝ) * (σ * (t * |f' (S i).1 - f (S i).1|))) / lam := by
    field_simp
  rw [eq, le_div_iff₀ hlam]
  linarith [key]
