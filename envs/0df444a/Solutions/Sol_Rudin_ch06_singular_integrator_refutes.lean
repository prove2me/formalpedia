-- Prove2me | solution 1 for Rudin.ch06_singular_integrator_refutes
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T17:05:22.514004+00:00
-- url     : https://prove2.me/submissions/694c4213-81d0-4548-ae58-c4ba817a4345

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace RudinSingularAux

open Rudin

/-- Division points of a partition increase with the index. -/
lemma x_mono {a b : ℝ} (P : Partition a b) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ P.n → P.x i ≤ P.x j := by
  intro i j hij hjn
  induction j with
  | zero =>
      have : i = 0 := Nat.le_zero.mp hij
      simp [this]
  | succ k ih =>
      have hk : k < P.n := hjn
      rcases Nat.eq_or_lt_of_le hij with h | h
      · exact le_of_eq (by rw [h])
      · have hik : i ≤ k := Nat.lt_succ_iff.mp h
        exact (ih hik (le_of_lt hk)).trans (P.mono k hk)

/-- Every division point lies in the interval. -/
lemma x_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  constructor
  · have h := x_mono P (Nat.zero_le i) hi
    rwa [P.first] at h
  · have h := x_mono P hi (le_refl P.n)
    rwa [P.last] at h

/-- The trivial partition of `[0, 1]` with a single subinterval. -/
def trivPart : Partition (0:ℝ) 1 where
  n := 1
  x := fun i => if i = 0 then 0 else 1
  first := by simp
  last := by norm_num
  mono := by
    intro i hi
    interval_cases i
    norm_num

lemma trivPart_x0 : trivPart.x 0 = 0 := rfl

lemma trivPart_x1 : trivPart.x 1 = 1 := rfl

section

variable {g : ℝ → ℝ}

/-- Every upper sum of a nonnegative integrand (with `α = id`) is nonnegative. -/
lemma upperSum_nonneg (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x) (P : Partition (0:ℝ) 1) :
    0 ≤ upperSum g id P := by
  refine Finset.sum_nonneg ?_
  intro i hi
  have hi' : i < P.n := Finset.mem_range.mp hi
  have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
  have hmi : P.x i ∈ Set.Icc (0:ℝ) 1 := x_mem P (le_of_lt hi')
  have hsup : 0 ≤ sSup (g '' Set.Icc (P.x i) (P.x (i + 1))) := by
    by_cases hb : BddAbove (g '' Set.Icc (P.x i) (P.x (i + 1)))
    · exact le_trans (hnn _ hmi) (le_csSup hb ⟨P.x i, ⟨le_rfl, hle⟩, rfl⟩)
    · simp [Real.sSup_of_not_bddAbove hb]
  have hfac : (0:ℝ) ≤ id (P.x (i + 1)) - id (P.x i) := by
    simpa using sub_nonneg.mpr hle
  exact mul_nonneg hsup hfac

/-- If a nonnegative integrand is unbounded above on `[0, 1]`, its upper integral is `0`:
the one-interval partition already gives the value `0`, and no upper sum is negative. -/
lemma upperIntegral_eq_zero (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x)
    (hunb : ¬ BddAbove (g '' Set.Icc (0:ℝ) 1)) : upperIntegral 0 1 g id = 0 := by
  have h0 : upperSum g id trivPart = 0 := by
    simp [upperSum, trivPart, Real.sSup_of_not_bddAbove hunb]
  have hmem : (0:ℝ) ∈ {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = upperSum g id P} := ⟨trivPart, h0.symm⟩
  have hlb : ∀ y ∈ {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = upperSum g id P}, (0:ℝ) ≤ y := by
    rintro y ⟨P, rfl⟩
    exact upperSum_nonneg hnn P
  refine le_antisymm (csInf_le ⟨0, fun y hy => hlb y hy⟩ hmem) (le_csInf ⟨0, hmem⟩ hlb)

/-- If a nonnegative function takes arbitrarily small values on every nondegenerate
subinterval, then its infimum over any such subinterval is `0`. -/
lemma sInf_eq_zero_of_small (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x)
    (hsmall : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, g x < ε)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) : sInf (g '' Set.Icc u v) = 0 := by
  have hsub : Set.Icc u v ⊆ Set.Icc (0:ℝ) 1 := Set.Icc_subset_Icc hu hv
  have hbdd : BddBelow (g '' Set.Icc u v) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hnn x (hsub hx)
  have hne : (g '' Set.Icc u v).Nonempty := ⟨g u, u, ⟨le_rfl, huv.le⟩, rfl⟩
  refine le_antisymm ?_ (le_csInf hne (by rintro _ ⟨x, hx, rfl⟩; exact hnn x (hsub hx)))
  by_contra hpos
  rw [not_le] at hpos
  obtain ⟨x, hx, hlt⟩ := hsmall u v hu huv hv _ hpos
  exact absurd (csInf_le hbdd ⟨x, hx, rfl⟩) (not_le.mpr hlt)

/-- Under the same hypotheses every lower sum vanishes. -/
lemma lowerSum_eq_zero (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x)
    (hsmall : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, g x < ε)
    (P : Partition (0:ℝ) 1) : lowerSum g id P = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hi' : i < P.n := Finset.mem_range.mp hi
  have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
  rcases eq_or_lt_of_le hle with h | h
  · simp [h]
  · have hmi : P.x i ∈ Set.Icc (0:ℝ) 1 := x_mem P (le_of_lt hi')
    have hmi1 : P.x (i + 1) ∈ Set.Icc (0:ℝ) 1 := x_mem P (Nat.succ_le_of_lt hi')
    have h0 := sInf_eq_zero_of_small hnn hsmall hmi.1 h hmi1.2
    simp [h0]

/-- Hence the lower integral vanishes too. -/
lemma lowerIntegral_eq_zero (hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x)
    (hsmall : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, g x < ε) :
    lowerIntegral 0 1 g id = 0 := by
  have hset : {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = lowerSum g id P} = {0} := by
    ext y
    constructor
    · rintro ⟨P, rfl⟩
      simp [lowerSum_eq_zero hnn hsmall P]
    · rintro rfl
      exact ⟨trivPart, (lowerSum_eq_zero hnn hsmall trivPart).symm⟩
  unfold lowerIntegral
  rw [hset, csSup_singleton]

end

/-- The upper sum of the constant integrand `1` telescopes. -/
lemma upperSum_one (β : ℝ → ℝ) (P : Partition (0:ℝ) 1) :
    upperSum (fun _ => (1:ℝ)) β P = β 1 - β 0 := by
  have hterm : ∀ i ∈ Finset.range P.n,
      sSup ((fun _ => (1:ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) * (β (P.x (i + 1)) - β (P.x i))
        = β (P.x (i + 1)) - β (P.x i) := by
    intro i hi
    have hle : P.x i ≤ P.x (i + 1) := P.mono i (Finset.mem_range.mp hi)
    have himg : ((fun _ => (1:ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) = {1} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨P.x i, ⟨le_rfl, hle⟩, rfl⟩, ?_⟩
      rintro _ ⟨x, _, rfl⟩
      rfl
    rw [himg, csSup_singleton, one_mul]
  rw [upperSum, Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun i => β (P.x i)),
    P.first, P.last]

/-- The lower sum of the constant integrand `1` telescopes. -/
lemma lowerSum_one (β : ℝ → ℝ) (P : Partition (0:ℝ) 1) :
    lowerSum (fun _ => (1:ℝ)) β P = β 1 - β 0 := by
  have hterm : ∀ i ∈ Finset.range P.n,
      sInf ((fun _ => (1:ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) * (β (P.x (i + 1)) - β (P.x i))
        = β (P.x (i + 1)) - β (P.x i) := by
    intro i hi
    have hle : P.x i ≤ P.x (i + 1) := P.mono i (Finset.mem_range.mp hi)
    have himg : ((fun _ => (1:ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) = {1} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨P.x i, ⟨le_rfl, hle⟩, rfl⟩, ?_⟩
      rintro _ ⟨x, _, rfl⟩
      rfl
    rw [himg, csInf_singleton, one_mul]
  rw [lowerSum, Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun i => β (P.x i)),
    P.first, P.last]

/-- The constant integrand `1` is integrable against any integrator, with integral
`β 1 - β 0`. -/
lemma rsIntegral_one (β : ℝ → ℝ) :
    RSIntegrable 0 1 (fun _ => (1:ℝ)) β ∧ RSIntegral 0 1 (fun _ => (1:ℝ)) β = β 1 - β 0 := by
  have hup : upperIntegral 0 1 (fun _ => (1:ℝ)) β = β 1 - β 0 := by
    have hset : {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = upperSum (fun _ => (1:ℝ)) β P}
        = {β 1 - β 0} := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        simp [upperSum_one β P]
      · rintro rfl
        exact ⟨trivPart, (upperSum_one β trivPart).symm⟩
    unfold upperIntegral
    rw [hset, csInf_singleton]
  have hlo : lowerIntegral 0 1 (fun _ => (1:ℝ)) β = β 1 - β 0 := by
    have hset : {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = lowerSum (fun _ => (1:ℝ)) β P}
        = {β 1 - β 0} := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        simp [lowerSum_one β P]
      · rintro rfl
        exact ⟨trivPart, (lowerSum_one β trivPart).symm⟩
    unfold lowerIntegral
    rw [hset, csSup_singleton]
  exact ⟨by unfold RSIntegrable; rw [hup, hlo], by unfold RSIntegral; exact hup⟩

/-- The zero integrand is Riemann integrable with integral `0`. -/
lemma riemann_zero :
    RiemannIntegrable 0 1 (fun _ => (0:ℝ)) ∧ RiemannIntegral 0 1 (fun _ => (0:ℝ)) = 0 := by
  have hup : upperIntegral 0 1 (fun _ => (0:ℝ)) id = 0 := by
    have hzero : ∀ P : Partition (0:ℝ) 1, upperSum (fun _ => (0:ℝ)) id P = 0 := by
      intro P
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hle : P.x i ≤ P.x (i + 1) := P.mono i (Finset.mem_range.mp hi)
      have himg : ((fun _ => (0:ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) = {0} := by
        refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨P.x i, ⟨le_rfl, hle⟩, rfl⟩, ?_⟩
        rintro _ ⟨x, _, rfl⟩
        rfl
      rw [himg, csSup_singleton, zero_mul]
    have hset : {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = upperSum (fun _ => (0:ℝ)) id P} = {0} := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        simp [hzero P]
      · rintro rfl
        exact ⟨trivPart, (hzero trivPart).symm⟩
    unfold upperIntegral
    rw [hset, csInf_singleton]
  have hlo : lowerIntegral 0 1 (fun _ => (0:ℝ)) id = 0 := by
    have hzero : ∀ P : Partition (0:ℝ) 1, lowerSum (fun _ => (0:ℝ)) id P = 0 := by
      intro P
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hle : P.x i ≤ P.x (i + 1) := P.mono i (Finset.mem_range.mp hi)
      have himg : ((fun _ => (0:ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) = {0} := by
        refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨P.x i, ⟨le_rfl, hle⟩, rfl⟩, ?_⟩
        rintro _ ⟨x, _, rfl⟩
        rfl
      rw [himg, csInf_singleton, zero_mul]
    have hset : {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = lowerSum (fun _ => (0:ℝ)) id P} = {0} := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        simp [hzero P]
      · rintro rfl
        exact ⟨trivPart, (hzero trivPart).symm⟩
    unfold lowerIntegral
    rw [hset, csSup_singleton]
  exact ⟨by unfold RiemannIntegrable RSIntegrable; rw [hup, hlo],
    by unfold RiemannIntegral RSIntegral; exact hup⟩

end RudinSingularAux

open Rudin RudinSingularAux

/-- A monotone, everywhere differentiable integrator whose derivative is unbounded above on
`[0,1]` and takes arbitrarily small values on every nondegenerate subinterval refutes the
unbounded forms of Rudin's Theorems 6.17, 6.21 and 6.22. -/
theorem solution (α : ℝ → ℝ) (hmono : Monotone α)
    (hdiff : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt α (deriv α x) x)
    (hgrow : α 0 < α 1)
    (hunb : ∀ K : ℝ, ∃ x ∈ Set.Icc (0:ℝ) 1, K < deriv α x)
    (hsmall : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, deriv α x < ε) :
    (¬ ∀ (a b : ℝ), a ≤ b → ∀ (f β : ℝ → ℝ), MonotoneOn β (Set.Icc a b) →
        (∀ x ∈ Set.Icc a b, HasDerivAt β (deriv β x) x) →
        RiemannIntegrable a b (deriv β) →
        (∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) →
        (RSIntegrable a b f β ↔ RiemannIntegrable a b (fun x => f x * deriv β x)) ∧
          (RSIntegrable a b f β →
            RSIntegral a b f β = RiemannIntegral a b (fun x => f x * deriv β x)))
    ∧ (¬ ∀ (a b : ℝ), a ≤ b → ∀ (f F : ℝ → ℝ), RiemannIntegrable a b f →
        (∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) → RiemannIntegral a b f = F b - F a)
    ∧ (¬ ∀ (a b : ℝ), a ≤ b → ∀ (F G f g : ℝ → ℝ),
        (∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) →
        (∀ x ∈ Set.Icc a b, HasDerivAt G (g x) x) →
        RiemannIntegrable a b f → RiemannIntegrable a b g →
        RiemannIntegral a b (fun x => F x * g x) =
          F b * G b - F a * G a - RiemannIntegral a b (fun x => f x * G x)) := by
  -- the derivative is nonnegative
  have hnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ deriv α x := fun x _ => hmono.deriv_nonneg
  -- it is unbounded above on `[0,1]`
  have hunb' : ¬ BddAbove (deriv α '' Set.Icc (0:ℝ) 1) := by
    rintro ⟨K, hK⟩
    obtain ⟨x, hx, hlt⟩ := hunb K
    exact absurd (hK ⟨x, hx, rfl⟩) (not_le.mpr hlt)
  have hup : upperIntegral 0 1 (deriv α) id = 0 := upperIntegral_eq_zero hnn hunb'
  have hlo : lowerIntegral 0 1 (deriv α) id = 0 := lowerIntegral_eq_zero hnn hsmall
  have hint : RiemannIntegrable 0 1 (deriv α) := by
    unfold RiemannIntegrable RSIntegrable
    rw [hup, hlo]
  have hval : RiemannIntegral 0 1 (deriv α) = 0 := by
    unfold RiemannIntegral RSIntegral
    exact hup
  obtain ⟨hone, honeval⟩ := rsIntegral_one α
  obtain ⟨hzero, hzeroval⟩ := riemann_zero
  refine ⟨?_, ?_, ?_⟩
  · -- Theorem 6.17
    intro h
    obtain ⟨-, h2⟩ := h 0 1 (by norm_num) (fun _ => (1:ℝ)) α (hmono.monotoneOn _) hdiff hint
      ⟨1, by intro x _; norm_num⟩
    have hfun : (fun x => (1:ℝ) * deriv α x) = deriv α := by
      funext x; rw [one_mul]
    have := h2 hone
    rw [honeval, hfun, hval] at this
    linarith
  · -- Theorem 6.21
    intro h
    have := h 0 1 (by norm_num) (deriv α) α hint hdiff
    rw [hval] at this
    linarith
  · -- Theorem 6.22
    intro h
    have hG : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun _ : ℝ => (1:ℝ)) ((fun _ : ℝ => (0:ℝ)) x) x := by
      intro x _
      simpa using (hasDerivAt_const x (1:ℝ))
    have hkey := h 0 1 (by norm_num) α (fun _ => (1:ℝ)) (deriv α) (fun _ => (0:ℝ)) hdiff hG
      hint hzero
    have h1 : (fun x => α x * (0:ℝ)) = (fun _ : ℝ => (0:ℝ)) := by
      funext x; rw [mul_zero]
    have h2 : (fun x => deriv α x * (1:ℝ)) = deriv α := by
      funext x; rw [mul_one]
    rw [h1, h2, hzeroval, hval] at hkey
    linarith
