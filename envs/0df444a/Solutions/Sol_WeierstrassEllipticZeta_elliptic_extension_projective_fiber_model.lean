-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_projective_fiber_model
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T17:52:58.171284+00:00
-- url     : https://prove2.me/submissions/d5c2e77a-4343-4790-864a-c074c012ab5a

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section
open WeierstrassEllipticZeta

private theorem base_smul (c : ℂˣ) (v : Fin 5 → ℂ) :
    extensionBaseVector (c • v) = c • extensionBaseVector v := by
  ext i
  fin_cases i <;> simp [extensionBaseVector, Units.smul_def]

private theorem shear_smul (u : ℂ) (c : ℂˣ) (v : Fin 5 → ℂ) :
    extensionFiberShear u (c • v) = c • extensionFiberShear u v := by
  ext i
  fin_cases i <;> simp [extensionFiberShear, Units.smul_def] <;> ring

private theorem shear_zero (v : Fin 5 → ℂ) : extensionFiberShear 0 v = v := by
  ext i
  fin_cases i <;> simp [extensionFiberShear]

private theorem shear_add (u t : ℂ) (v : Fin 5 → ℂ) :
    extensionFiberShear (u + t) v = extensionFiberShear u (extensionFiberShear t v) := by
  ext i
  fin_cases i <;> simp [extensionFiberShear] <;> ring

private theorem cover_ne (v : Fin 5 → ℂ) (h : v 0 ≠ 0 ∨ v 2 ≠ 0) : v ≠ 0 := by
  intro heq
  rcases h with h | h <;> simp_all

private def pointOfVector (g₂ g₃ : ℂ) (v : Fin 5 → ℂ)
    (hq : MvPolynomial.eval v extensionQuadric = 0)
    (hc : MvPolynomial.eval v (extensionCubic g₂ g₃) = 0)
    (h : v 0 ≠ 0 ∨ v 2 ≠ 0) : ProjectiveExtensionChartLocus g₂ g₃ := by
  let p := Projectivization.mk ℂ v (cover_ne v h)
  refine ⟨⟨p, ?_, ?_⟩, ?_⟩
  · obtain ⟨c, heq⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v (cover_ne v h)
    rw [← heq]
    simp [extensionQuadric, Units.smul_def] at hq ⊢
    linear_combination (c : ℂ) ^ 2 * hq
  · obtain ⟨c, heq⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v (cover_ne v h)
    rw [← heq]
    simp [extensionCubic, Units.smul_def] at hc ⊢
    linear_combination (c : ℂ) ^ 3 * hc
  · obtain ⟨c, heq⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v (cover_ne v h)
    change p.rep 0 ≠ 0 ∨ p.rep 2 ≠ 0
    rw [← heq]
    change (c : ℂ) * v 0 ≠ 0 ∨ (c : ℂ) * v 2 ≠ 0
    exact h.imp (mul_ne_zero c.ne_zero) (mul_ne_zero c.ne_zero)

private theorem pointOfVector_val (g₂ g₃ : ℂ) (v : Fin 5 → ℂ)
    (hq : MvPolynomial.eval v extensionQuadric = 0)
    (hc : MvPolynomial.eval v (extensionCubic g₂ g₃) = 0)
    (h : v 0 ≠ 0 ∨ v 2 ≠ 0) :
    (pointOfVector g₂ g₃ v hq hc h).val.val =
      Projectivization.mk ℂ v (cover_ne v h) := rfl

private theorem locus_ext {g₂ g₃ : ℂ} {p q : ProjectiveExtensionChartLocus g₂ g₃}
    (h : p.val.val = q.val.val) : p = q := Subtype.ext (Subtype.ext h)

theorem solution (g₂ g₃ : ℂ) :
    Nonempty (ProjectiveExtensionFiberModel g₂ g₃) := by
  classical
  let Z := ProjectiveExtensionChartLocus g₂ g₃
  have base_ne (p : Z) : extensionBaseVector p.val.val.rep ≠ 0 := by
    intro heq
    have h0 := congrFun heq 0
    have h2 := congrFun heq 2
    rcases p.property with h | h <;> simp_all [extensionBaseVector]
  let π (p : Z) := Projectivization.mk ℂ (extensionBaseVector p.val.val.rep) (base_ne p)
  have π_coords (p : Z) (v : Fin 5 → ℂ) (hv : v ≠ 0)
      (heq : p.val.val = Projectivization.mk ℂ v hv) (hb : extensionBaseVector v ≠ 0) :
      π p = Projectivization.mk ℂ (extensionBaseVector v) hb := by
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
    apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).2
    exact ⟨c, by rw [heq, ← hc, base_smul]⟩
  have shear_cover (u : ℂ) (p : Z) :
      (extensionFiberShear u p.val.val.rep) 0 ≠ 0 ∨
        (extensionFiberShear u p.val.val.rep) 2 ≠ 0 := by
    simpa [extensionFiberShear] using p.property
  have shear_quadric (u : ℂ) (p : Z) :
      MvPolynomial.eval (extensionFiberShear u p.val.val.rep) extensionQuadric = 0 := by
    have hq := p.val.property.1
    simp [extensionQuadric, extensionFiberShear] at hq ⊢
    linear_combination hq
  have shear_cubic (u : ℂ) (p : Z) :
      MvPolynomial.eval (extensionFiberShear u p.val.val.rep) (extensionCubic g₂ g₃) = 0 := by
    simpa [extensionCubic, extensionFiberShear] using p.val.property.2
  let A (u : ℂ) (p : Z) := pointOfVector g₂ g₃ (extensionFiberShear u p.val.val.rep)
    (shear_quadric u p) (shear_cubic u p) (shear_cover u p)
  have A_coords (u : ℂ) (p : Z) :
      (A u p).val.val = Projectivization.mk ℂ (extensionFiberShear u p.val.val.rep)
        (cover_ne _ (shear_cover u p)) := pointOfVector_val ..
  have A_rep (u : ℂ) (p : Z) (v : Fin 5 → ℂ) (hv : v ≠ 0)
      (heq : p.val.val = Projectivization.mk ℂ v hv)
      (hs : extensionFiberShear u v ≠ 0) :
      (A u p).val.val = Projectivization.mk ℂ (extensionFiberShear u v) hs := by
    rw [A_coords]
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
    apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).2
    exact ⟨c, by rw [heq, ← hc, shear_smul]⟩
  have A_zero (p : Z) : A 0 p = p := by
    apply locus_ext
    simpa only [shear_zero, Projectivization.mk_rep] using A_coords 0 p
  have A_add (u t : ℂ) (p : Z) : A (u + t) p = A u (A t p) := by
    apply locus_ext
    have hne : extensionFiberShear u (extensionFiberShear t p.val.val.rep) ≠ 0 := by
      rw [← shear_add]
      exact cover_ne _ (shear_cover (u + t) p)
    rw [A_rep u (A t p) _ _ (A_coords t p) hne, A_coords]
    congr 1
    exact shear_add u t p.val.val.rep
  have π_A (u : ℂ) (p : Z) : π (A u p) = π p := by
    have hb : extensionBaseVector (extensionFiberShear u p.val.val.rep) ≠ 0 := by
      simpa [extensionBaseVector, extensionFiberShear] using base_ne p
    rw [π_coords (A u p) _ _ (A_coords u p) hb]
    rfl
  have A_free (p : Z) (u t : ℂ) (heq : A u p = A t p) : u = t := by
    have heq' := congrArg (fun q : Z => q.val.val) heq
    rw [A_coords, A_coords] at heq'
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).1 heq'
    have h0 := congrFun hc 0
    have h2 := congrFun hc 2
    have h3 := congrFun hc 3
    have h4 := congrFun hc 4
    simp [extensionFiberShear, Units.smul_def] at h0 h2 h3 h4
    have hc1 : (c : ℂ) = 1 := by
      rcases p.property with h | h
      · exact mul_right_cancel₀ h (by simpa using h0)
      · exact mul_right_cancel₀ h (by simpa using h2)
    simp only [hc1, one_mul] at h3 h4
    rcases p.property with h | h
    · exact mul_right_cancel₀ h (add_left_cancel h3).symm
    · exact mul_right_cancel₀ h (add_left_cancel h4).symm
  have π_cubic (p : Z) : extensionBaseCubic g₂ g₃ (π p).rep = 0 := by
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (extensionBaseVector p.val.val.rep) (base_ne p)
    change extensionBaseCubic g₂ g₃ (Projectivization.mk ℂ _ _).rep = 0
    rw [← hc]
    have hp := p.val.property.2
    simp [extensionCubic] at hp
    simp [extensionBaseCubic, extensionBaseVector, Units.smul_def]
    linear_combination (c : ℂ) ^ 3 * hp
  have π_surjective (b : Projectivization ℂ (Fin 3 → ℂ))
      (hb : extensionBaseCubic g₂ g₃ b.rep = 0) : ∃ p, π p = b := by
    have cover : b.rep 0 ≠ 0 ∨ b.rep 2 ≠ 0 := by
      by_cases h0 : b.rep 0 = 0
      · right
        intro h2
        have h1 : b.rep 1 = 0 := by
          simpa [extensionBaseCubic, h0, h2] using hb
        apply b.rep_nonzero
        ext i
        fin_cases i <;> simp_all
      · exact Or.inl h0
    suffices ∃ (v : Fin 5 → ℂ) (hq : MvPolynomial.eval v extensionQuadric = 0)
        (hc : MvPolynomial.eval v (extensionCubic g₂ g₃) = 0)
        (h : v 0 ≠ 0 ∨ v 2 ≠ 0), extensionBaseVector v = b.rep by
      obtain ⟨v, hq, hc, h, heq⟩ := this
      let p := pointOfVector g₂ g₃ v hq hc h
      have hn : extensionBaseVector v ≠ 0 := heq ▸ b.rep_nonzero
      refine ⟨p, ?_⟩
      rw [π_coords p _ _ (pointOfVector_val ..) hn]
      simpa only [heq] using b.mk_rep
    rcases cover with h | h
    · let v : Fin 5 → ℂ := ![b.rep 0, b.rep 1, b.rep 2, 0, 2 * b.rep 1 ^ 2 / b.rep 0]
      refine ⟨v, ?_, ?_, Or.inl h, ?_⟩
      · simp [v, extensionQuadric]
        field_simp
        ring
      · simpa [v, extensionCubic, extensionBaseCubic] using hb
      · ext i
        fin_cases i <;> rfl
    · let v : Fin 5 → ℂ := ![b.rep 0, b.rep 1, b.rep 2, -(2 * b.rep 1 ^ 2 / b.rep 2), 0]
      refine ⟨v, ?_, ?_, Or.inr h, ?_⟩
      · simp [v, extensionQuadric]
        field_simp
        ring
      · simpa [v, extensionCubic, extensionBaseCubic] using hb
      · ext i
        fin_cases i <;> rfl
  have transitive (p q : Z) (heq : π p = π q) : ∃ u : ℂ, A u p = q := by
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).1 heq
    let w : Fin 5 → ℂ := c • q.val.val.rep
    have hw : extensionBaseVector w = extensionBaseVector p.val.val.rep := by
      rw [base_smul]
      exact hc
    have h0 : w 0 = p.val.val.rep 0 := congrFun hw 0
    have h1 : w 1 = p.val.val.rep 1 := congrFun hw 1
    have h2 : w 2 = p.val.val.rep 2 := congrFun hw 2
    have hq : w 0 * w 4 - w 2 * w 3 - 2 * w 1 ^ 2 = 0 := by
      have hq := q.val.property.1
      simp [extensionQuadric] at hq
      simp [w, Units.smul_def]
      linear_combination (c : ℂ) ^ 2 * hq
    have hp := p.val.property.1
    simp [extensionQuadric] at hp
    rw [h0, h1, h2] at hq
    have hdiff : p.val.val.rep 0 * (w 4 - p.val.val.rep 4) =
        p.val.val.rep 2 * (w 3 - p.val.val.rep 3) := by
      linear_combination hq - hp
    suffices ∃ u : ℂ, extensionFiberShear u p.val.val.rep = w by
      obtain ⟨u, hu⟩ := this
      refine ⟨u, locus_ext ?_⟩
      rw [A_coords, ← q.val.val.mk_rep]
      exact (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).2 ⟨c, hu.symm⟩
    rcases p.property with h | h
    · refine ⟨(w 3 - p.val.val.rep 3) / p.val.val.rep 0, ?_⟩
      ext i
      fin_cases i
      · exact h0.symm
      · exact h1.symm
      · exact h2.symm
      · simp [extensionFiberShear, h]
      · change p.val.val.rep 4 + ((w 3 - p.val.val.rep 3) / p.val.val.rep 0) *
          p.val.val.rep 2 = w 4
        apply (mul_left_cancel₀ h)
        field_simp
        linear_combination -hdiff
    · refine ⟨(w 4 - p.val.val.rep 4) / p.val.val.rep 2, ?_⟩
      ext i
      fin_cases i
      · exact h0.symm
      · exact h1.symm
      · exact h2.symm
      · change p.val.val.rep 3 + ((w 4 - p.val.val.rep 4) / p.val.val.rep 2) *
          p.val.val.rep 0 = w 3
        apply (mul_left_cancel₀ h)
        field_simp
        linear_combination hdiff
      · simp [extensionFiberShear, h]
  refine ⟨{
    projection := π
    action := A
    projection_coords := fun p => ⟨base_ne p, rfl⟩
    projection_cubic := π_cubic
    projection_surjective := π_surjective
    action_coords := fun u p => ⟨_, A_coords u p⟩
    zero_action := A_zero
    add_action := A_add
    fiber := ?_ }⟩
  intro p q
  constructor
  · intro h
    obtain ⟨u, hu⟩ := transitive p q h
    exact ⟨u, hu, fun t ht => A_free p t u (ht.trans hu.symm)⟩
  · rintro ⟨u, rfl, _⟩
    exact (π_A u p).symm

