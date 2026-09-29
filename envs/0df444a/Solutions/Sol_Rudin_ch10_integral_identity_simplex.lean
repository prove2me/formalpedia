-- Prove2me | solution 1 for Rudin.ch10_integral_identity_simplex
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T03:24:17.569744+00:00
-- url     : https://prove2.me/submissions/ca1551e0-0fd1-402b-bdd0-fb6d71d3a99e

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory Matrix Set

namespace Rudin



lemma isClosed_stdSimplex (k : ℕ) : IsClosed (stdSimplex k) := by
  have h1 : IsClosed {u : Fin k → ℝ | ∀ i, 0 ≤ u i} := by
    have h : {u : Fin k → ℝ | ∀ i, 0 ≤ u i} = ⋂ i : Fin k, {u : Fin k → ℝ | 0 ≤ u i} := by
      ext u; simp
    rw [h]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {u : Fin k → ℝ | ∑ i, u i ≤ 1} :=
    isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

lemma measurableSet_stdSimplex (k : ℕ) : MeasurableSet (stdSimplex k) :=
  (isClosed_stdSimplex k).measurableSet

lemma isCompact_stdSimplex (k : ℕ) : IsCompact (stdSimplex k) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨isClosed_stdSimplex k, ?_⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, fun u hu => ?_⟩
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
  calc u i ≤ ∑ j, u j := Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)
    _ ≤ 1 := hu.2






/-- The partial derivatives of a coordinate function. -/
lemma partialDeriv_coord {k : ℕ} (i s : Fin k) (u : Fin k → ℝ) :
    partialDeriv (fun v : Fin k → ℝ => v i) s u = if i = s then 1 else 0 := by
  have h : (fun v : Fin k → ℝ => v i) = (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ) := rfl
  rw [partialDeriv, h, ContinuousLinearMap.fderiv]
  simp [Pi.single_apply]

/-- The Jacobian of the identity map along an index tuple is the sign of the tuple when the
tuple is a permutation, and zero otherwise. -/
lemma jacobian_id_eq {k : ℕ} (I : Fin k → Fin k) (u : Fin k → ℝ) :
    jacobian (id : (Fin k → ℝ) → (Fin k → ℝ)) I u
      = if h : Function.Bijective I then ((Equiv.Perm.sign (Equiv.ofBijective I h) : ℤ) : ℝ)
        else 0 := by
  have hmat : (Matrix.of fun r s : Fin k => partialDeriv (fun v => (id v) (I r)) s u)
      = Matrix.of fun r s => if I r = s then (1 : ℝ) else 0 := by
    ext r s
    exact partialDeriv_coord (I r) s u
  rw [jacobian, hmat]
  by_cases h : Function.Bijective I
  · rw [dif_pos h]
    have hp : (Matrix.of fun r s : Fin k => if I r = s then (1 : ℝ) else 0)
        = (Equiv.ofBijective I h).toPEquiv.toMatrix := by
      ext r s
      simp [PEquiv.toMatrix, Equiv.toPEquiv, Equiv.ofBijective]
    rw [hp, Matrix.det_permutation]
  · rw [dif_neg h]
    have hinj : ¬ Function.Injective I := fun hi => h ⟨hi, Finite.surjective_of_injective hi⟩
    rw [Function.not_injective_iff] at hinj
    obtain ⟨r, r', hIr, hrr'⟩ := hinj
    refine Matrix.det_zero_of_row_eq hrr' ?_
    funext s
    simp [hIr]

/-- A sum over all index tuples weighted by the sign of the bijective ones is a sum over
permutations. -/
lemma sum_bijective_perm {k : ℕ} (g : (Fin k → Fin k) → ℝ) :
    (∑ I : Fin k → Fin k, if h : Function.Bijective I then
        g I * ((Equiv.Perm.sign (Equiv.ofBijective I h) : ℤ) : ℝ) else 0)
      = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℝ) * g (⇑σ) := by
  classical
  set F : (Fin k → Fin k) → ℝ := fun I => if h : Function.Bijective I then
      g I * ((Equiv.Perm.sign (Equiv.ofBijective I h) : ℤ) : ℝ) else 0 with hF
  have key : (Finset.univ : Finset (Fin k → Fin k)).sum F
      = ((Finset.univ : Finset (Fin k → Fin k)).filter fun I => Function.Bijective I).sum F := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro I _ hI
    have hb : ¬ Function.Bijective I := fun hb => hI (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)
    simp only [dif_neg hb]
  rw [key]
  refine (Finset.sum_nbij' (fun σ : Equiv.Perm (Fin k) => (⇑σ : Fin k → Fin k))
    (fun I => if h : Function.Bijective I then Equiv.ofBijective I h else 1)
    (fun σ _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, σ.bijective⟩)
    (fun I _ => Finset.mem_univ _) ?_ ?_ ?_).symm
  · intro σ _
    show (if h : Function.Bijective (⇑σ) then Equiv.ofBijective (⇑σ) h else 1) = σ
    rw [dif_pos σ.bijective]
    exact Equiv.coe_inj.mp rfl
  · intro I hI
    have hb := (Finset.mem_filter.1 hI).2
    show ⇑(if h : Function.Bijective I then Equiv.ofBijective I h else 1) = I
    rw [dif_pos hb]
    rfl
  · intro σ _
    show ((Equiv.Perm.sign σ : ℤ) : ℝ) * g (⇑σ) = F (⇑σ)
    simp only [hF, dif_pos σ.bijective]
    rw [show Equiv.ofBijective (⇑σ) σ.bijective = σ from Equiv.coe_inj.mp rfl]
    ring

/-- The integral of a `k`-form over the identity surface of `Qᵏ` is the integral over `Qᵏ` of
the alternating sum of its coefficients. -/
theorem integralOverSimplex_id {k : ℕ} (ω : KForm k k) :
    integralOverSimplex ω ⟨id⟩
      = ∫ u in stdSimplex k,
          ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ω.coeff (⇑σ) u := by
  refine setIntegral_congr_fun (measurableSet_stdSimplex k) fun u _ => ?_
  rw [← sum_bijective_perm fun I => ω.coeff I u]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [jacobian_id_eq I u]
  by_cases h : Function.Bijective I
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h, mul_zero]


end Rudin

theorem solution (k : ℕ) (ω : Rudin.KForm k k) :
    Rudin.integralOverSimplex ω ⟨id⟩
      = ∫ u in Rudin.stdSimplex k,
          ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ω.coeff (⇑σ) u :=
  Rudin.integralOverSimplex_id ω
