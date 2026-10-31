-- Prove2me | solution 1 for TalagrandConc.Assignment.theorem_10_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T17:34:56.906175+00:00
-- url     : https://prove2.me/submissions/43b35ad8-0a56-4a55-8217-b39d623d70f4

import Mathlib
import Definitions.Def_TalagrandConc_Assignment_Basic

section

open scoped BigOperators
open MeasureTheory

namespace TalagrandConc.Assignment.ACFresh

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

/-- Coordinatewise upper cap; no probabilistic assumptions. -/
def cappedCosts {N : ℕ} (b : ℝ) (X : Fin N × Fin N → ℝ) :
    Fin N × Fin N → ℝ := fun p => min (X p) b

lemma optCost_le_assignmentCost {N : ℕ} (X : Fin N × Fin N → ℝ)
    (τ : Equiv.Perm (Fin N)) : optCost X ≤ assignmentCost X τ := by
  classical
  exact Finset.inf'_le _ (Finset.mem_univ τ)

lemma exists_optimal_assignment {N : ℕ} (X : Fin N × Fin N → ℝ) :
    ∃ τ : Equiv.Perm (Fin N), assignmentCost X τ = optCost X ∧ IsOptimalAssignment X τ := by
  classical
  obtain ⟨τ, _, hτ⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (Equiv.Perm (Fin N)))) Finset.univ_nonempty
    (fun τ => assignmentCost X τ)
  refine ⟨τ, hτ.symm, ?_⟩
  intro σ
  rw [hτ.symm]
  exact optCost_le_assignmentCost X σ

lemma optCost_mono {N : ℕ} {X Y : Fin N × Fin N → ℝ} (h : ∀ p, X p ≤ Y p) :
    optCost X ≤ optCost Y := by
  obtain ⟨τ,hτ,_⟩ := exists_optimal_assignment Y
  rw [← hτ]
  exact (optCost_le_assignmentCost X τ).trans (Finset.sum_le_sum fun i _ => h (i,τ i))

lemma cappedCosts_mem_Icc {N : ℕ} {b : ℝ} (hb : 0 ≤ b)
    {X : Fin N × Fin N → ℝ} (hX : ∀ p, X p ∈ Set.Icc (0:ℝ) 1) :
    ∀ p, cappedCosts b X p ∈ Set.Icc (0:ℝ) 1 := by
  intro p
  exact ⟨le_min (hX p).1 hb, (min_le_left _ _).trans (hX p).2⟩

lemma capped_optCost_le {N : ℕ} (b : ℝ) (X : Fin N × Fin N → ℝ) :
    optCost (cappedCosts b X) ≤ optCost X :=
  optCost_mono (fun _ => min_le_left _ _)

lemma capped_optCost_eq_of_optimal_below {N : ℕ} {b v : ℝ} (hvb : v < b)
    (X : Fin N × Fin N → ℝ)
    (hbound : ∀ τ : Equiv.Perm (Fin N), IsOptimalAssignment (cappedCosts b X) τ →
      ∀ i, cappedCosts b X (i,τ i) ≤ v) :
    optCost (cappedCosts b X) = optCost X := by
  obtain ⟨τ,hτ,hopt⟩ := exists_optimal_assignment (cappedCosts b X)
  have he : assignmentCost (cappedCosts b X) τ = assignmentCost X τ := by
    apply Finset.sum_congr rfl
    intro i _
    have hi := (hbound τ hopt i).trans_lt hvb
    have hx : X (i,τ i) < b := by
      by_contra hn
      have hbx : b ≤ X (i,τ i) := le_of_not_gt hn
      simp only [cappedCosts, min_eq_right hbx] at hi
      exact (lt_irrefl b) hi
    exact min_eq_left hx.le
  apply le_antisymm (capped_optCost_le b X)
  rw [← hτ, he]
  exact optCost_le_assignmentCost X τ

lemma capped_digraphU_eq {N : ℕ} (X : Fin N × Fin N → ℝ) (u b : ℝ)
    (hb : 2*u*(N:ℝ)⁻¹*Real.log N < b) :
    digraphU N u (cappedCosts b X) = digraphU N u X := by
  ext p
  change min (X p) b ≤ 2*u*(N:ℝ)⁻¹*Real.log N ↔ X p ≤ 2*u*(N:ℝ)⁻¹*Real.log N
  exact min_le_iff.trans (or_iff_left (not_le_of_gt hb))

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ) : ℝ :=
  ∑ a, w a * f a

lemma finiteMean_nonneg {Ω : Type*} [Fintype Ω] {w f : Ω → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hf : ∀ a, 0 ≤ f a) : 0 ≤ finiteMean w f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (hf a)

lemma finiteMean_mono {Ω : Type*} [Fintype Ω] {w f g : Ω → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hfg : ∀ a, f a ≤ g a) :
    finiteMean w f ≤ finiteMean w g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hfg a) (hw a)

lemma finiteMean_const {Ω : Type*} [Fintype Ω] {w : Ω → ℝ}
    (hw : ∑ a, w a = 1) (c : ℝ) : finiteMean w (fun _ => c) = c := by
  simp only [finiteMean, ← Finset.sum_mul, hw, one_mul]

lemma finiteMean_add {Ω : Type*} [Fintype Ω] (w f g : Ω → ℝ) :
    finiteMean w (fun a => f a + g a) = finiteMean w f + finiteMean w g := by
  simp only [finiteMean, mul_add, Finset.sum_add_distrib]

lemma finiteMean_mul_const {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ) (c : ℝ) :
    finiteMean w (fun a => f a * c) = finiteMean w f * c := by
  simp only [finiteMean, ← mul_assoc, Finset.sum_mul]

lemma finiteMean_pos {Ω : Type*} [Fintype Ω] {w f : Ω → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (hf : ∀ a, 0 < f a) :
    0 < finiteMean w f := by
  have hex : ∃ a, 0 < w a := by
    by_contra h
    have hz : ∀ a, w a = 0 := fun a => le_antisymm (not_lt.mp (fun ha => h ⟨a, ha⟩)) (hw a)
    simp [hz] at hs
  obtain ⟨a, ha⟩ := hex
  exact Finset.sum_pos' (fun b _ => mul_nonneg (hw b) (hf b).le)
    ⟨a, Finset.mem_univ a, mul_pos ha (hf a)⟩

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

noncomputable def productWeight {α : Type*} (p : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ :=
  ∏ i, p (x i)

lemma productWeight_nonneg {α : Type*} {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (n : ℕ) (x : Fin n → α) : 0 ≤ productWeight p n x :=
  Finset.prod_nonneg fun i _ => hp (x i)

lemma productWeight_sum {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∑ a, p a = 1) (n : ℕ) : ∑ x, productWeight p n x = 1 := by
  unfold productWeight
  rw [← Fintype.sum_pow p n,hp,one_pow]

lemma productWeight_snoc {α : Type*} (p : α → ℝ) {n : ℕ} (x : Fin n → α) (a : α) :
    productWeight p (n+1) (Fin.snoc x a) = productWeight p n x*p a := by
  simp [productWeight,Fin.prod_univ_castSucc]

noncomputable def productMean {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ)
    (f : (Fin n → α) → ℝ) : ℝ := finiteMean (productWeight p n) f

lemma productMean_succ {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ)
    (f : (Fin (n+1) → α) → ℝ) :
    productMean p (n+1) f = finiteMean p (fun a => productMean p n (fun x => f (Fin.snoc x a))) := by
  unfold productMean finiteMean
  rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => α)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change productWeight p (n+1) (Fin.snoc x a)*f (Fin.snoc x a) = _
  rw [productWeight_snoc]
  ring

lemma productMean_zero {α : Type*} [Fintype α] (p : α → ℝ) (f : (Fin 0 → α) → ℝ) :
    productMean p 0 f = f Fin.elim0 := by
  simp [productMean,finiteMean,productWeight]
  congr 1

noncomputable def productMass {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ)
    (A : Set (Fin n → α)) : ℝ := by
  classical
  exact productMean p n (fun x => if x ∈ A then 1 else 0)

lemma productMass_nonneg {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (n : ℕ) (A : Set (Fin n → α)) : 0 ≤ productMass p n A := by
  classical
  exact finiteMean_nonneg (productWeight_nonneg hp n) (by intro x; split_ifs <;> norm_num)

lemma productMass_mono {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) {n : ℕ} {A B : Set (Fin n → α)} (hAB : A ⊆ B) :
    productMass p n A ≤ productMass p n B := by
  classical
  apply finiteMean_mono (productWeight_nonneg hp n)
  intro x
  by_cases hx : x ∈ A
  · simp [hx,hAB hx]
  · simp only [hx,ite_false]
    split_ifs <;> norm_num

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal BigOperators
namespace TalagrandConc.Assignment.ACFresh

abbrev edgeEquiv (N : ℕ) : Fin (N*N) ≃ Fin N × Fin N := finProdFinEquiv.symm

noncomputable def intervalLaw : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
instance intervalLaw_probability : IsProbabilityMeasure intervalLaw := by
  constructor
  simp [intervalLaw, Real.volume_Icc]

noncomputable def cubeLaw (n : ℕ) : Measure (Fin n → unitInterval) :=
  Measure.pi (fun _ => volume)
instance cubeLaw_probability (n : ℕ) : IsProbabilityMeasure (cubeLaw n) := by
  unfold cubeLaw
  infer_instance
instance costLaw_probability (N : ℕ) : IsProbabilityMeasure (costLaw N) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin N × Fin N => intervalLaw))
  infer_instance

noncomputable def cubeLift (N : ℕ) (x : Fin (N*N) → unitInterval) : Fin N × Fin N → ℝ :=
  fun e => (x ((edgeEquiv N).symm e) : ℝ)

lemma cubeLift_preserving (N : ℕ) : MeasurePreserving (cubeLift N) (cubeLaw (N*N)) (costLaw N) := by
  have hc := measurePreserving_pi (fun _ : Fin (N*N) => (volume : Measure unitInterval))
    (fun _ => intervalLaw) (fun _ => unitInterval.measurePreserving_coe)
  have hr := measurePreserving_piCongrLeft (fun _ : Fin N × Fin N => intervalLaw) (edgeEquiv N)
  convert hr.comp hc using 1
  · ext x e
    simp [cubeLift,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  · rfl
  · rfl


lemma continuous_cubeLift (N : ℕ) : Continuous (cubeLift N) := by
  unfold cubeLift
  fun_prop

noncomputable def thresholdSample (N : ℕ) (p : ℝ) (X : Fin N × Fin N → ℝ) :
    Fin (N*N) → Bool := fun i => decide (X (edgeEquiv N i) ≤ p)

noncomputable def bernoulliWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

lemma bernoulliWeight_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∀ b, 0 ≤ bernoulliWeight p b := by
  intro b
  cases b <;> simp [bernoulliWeight,h0,sub_nonneg.mpr h1]

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

abbrev Pattern (n : ℕ) := Fin n → Bool

def bitVector {n : ℕ} (u : Pattern n) : Fin n → ℝ := fun i => if u i then 1 else 0

noncomputable def sqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, v i ^ 2

lemma sqNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (v i)

lemma continuous_sqNorm (n : ℕ) : Continuous (sqNorm (n := n)) := by
  unfold sqNorm
  fun_prop

noncomputable def patternHull {n : ℕ} (U : Finset (Pattern n)) : Set (Fin n → ℝ) :=
  convexHull ℝ (bitVector '' (U : Set (Pattern n)))

lemma patternHull_compact {n : ℕ} (U : Finset (Pattern n)) : IsCompact (patternHull U) :=
  (U.finite_toSet.image bitVector).isCompact_convexHull (𝕜 := ℝ)

lemma patternHull_nonempty {n : ℕ} {U : Finset (Pattern n)} (hU : U.Nonempty) :
    (patternHull U).Nonempty := by
  obtain ⟨u, hu⟩ := hU
  exact ⟨bitVector u, subset_convexHull ℝ _ ⟨u, hu, rfl⟩⟩

lemma exists_patternMin {n : ℕ} {U : Finset (Pattern n)} (hU : U.Nonempty) :
    ∃ v ∈ patternHull U, ∀ w ∈ patternHull U, sqNorm v ≤ sqNorm w := by
  exact (patternHull_compact U).exists_isMinOn (patternHull_nonempty hU)
    (continuous_sqNorm n).continuousOn

noncomputable def patternMin {n : ℕ} (U : Finset (Pattern n)) (hU : U.Nonempty) : Fin n → ℝ :=
  Classical.choose (exists_patternMin hU)

lemma patternMin_spec {n : ℕ} (U : Finset (Pattern n)) (hU : U.Nonempty) :
    patternMin U hU ∈ patternHull U ∧
      ∀ w ∈ patternHull U, sqNorm (patternMin U hU) ≤ sqNorm w :=
  Classical.choose_spec (exists_patternMin hU)

noncomputable def patternDistance {n : ℕ} (U : Finset (Pattern n)) : ℝ :=
  if hU : U.Nonempty then sqNorm (patternMin U hU) else n

lemma patternDistance_eq {n : ℕ} {U : Finset (Pattern n)} (hU : U.Nonempty) :
    patternDistance U = sqNorm (patternMin U hU) := by simp [patternDistance, hU]

lemma patternDistance_nonneg {n : ℕ} (U : Finset (Pattern n)) : 0 ≤ patternDistance U := by
  unfold patternDistance
  split_ifs
  · exact sqNorm_nonneg _
  · positivity

lemma patternDistance_le {n : ℕ} {U : Finset (Pattern n)} (hU : U.Nonempty)
    {v : Fin n → ℝ} (hv : v ∈ patternHull U) : patternDistance U ≤ sqNorm v := by
  rw [patternDistance_eq hU]
  exact (patternMin_spec U hU).2 v hv

lemma patternDistance_antitone {n : ℕ} {U V : Finset (Pattern n)}
    (hU : U.Nonempty) (hUV : U ⊆ V) : patternDistance V ≤ patternDistance U := by
  have hV := hU.mono hUV
  rw [patternDistance_eq hU]
  apply patternDistance_le hV
  exact convexHull_mono (Set.image_mono hUV) (patternMin_spec U hU).1

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma patternDistance_le_dimension {n : ℕ} (U : Finset (Pattern n)) :
    patternDistance U ≤ n := by
  by_cases hU : U.Nonempty
  · have hUne := hU
    obtain ⟨u, hu⟩ := hU
    apply (patternDistance_le hUne (subset_convexHull ℝ _ ⟨u, hu, rfl⟩)).trans
    calc
      sqNorm (bitVector u) ≤ ∑ _i : Fin n, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [bitVector]
        split_ifs <;> norm_num
      _ = n := by simp
  · simp [patternDistance, hU]

lemma convex_dot_superlevel {n : ℕ} (a : Fin n → ℝ) (c : ℝ) :
    Convex ℝ {v : Fin n → ℝ | c ≤ ∑ i, a i*v i} := by
  intro x hx y hy s t hs ht hst
  change c ≤ ∑ i, a i*(s*x i+t*y i)
  have he : (∑ i, a i*(s*x i+t*y i)) = s*(∑ i,a i*x i)+t*(∑ i,a i*y i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  change c ≤ ∑ i, a i*x i at hx
  change c ≤ ∑ i, a i*y i at hy
  have hc : s*c+t*c=c := by rw [← add_mul,hst,one_mul]
  linarith [mul_le_mul_of_nonneg_left hx hs,mul_le_mul_of_nonneg_left hy ht]

lemma pattern_weight_witness {n : ℕ} {U : Finset (Pattern n)} (hU : U.Nonempty)
    (a : Fin n → ℝ) : ∃ u ∈ U,
      (∑ i, a i*bitVector u i) ≤ Real.sqrt (sqNorm a)*Real.sqrt (patternDistance U) := by
  obtain ⟨u, hu, hmin⟩ := U.exists_min_image (fun u => ∑ i, a i*bitVector u i) hU
  refine ⟨u, hu, ?_⟩
  have hh : patternHull U ⊆ {v | (∑ i,a i*bitVector u i) ≤ ∑ i,a i*v i} := by
    apply convexHull_min
    · rintro _ ⟨v,hv,rfl⟩
      exact hmin v hv
    · exact convex_dot_superlevel _ _
  have h := hh (patternMin_spec U hU).1
  apply h.trans
  rw [patternDistance_eq hU]
  exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a (patternMin U hU)

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

noncomputable def mismatchPatterns {α : Type*} {n : ℕ}
    (A : Set (Fin n → α)) (x : Fin n → α) : Finset (Pattern n) := by
  classical
  exact Finset.univ.filter fun u => ∃ y ∈ A, ∀ i, u i = false → x i = y i

lemma mem_mismatchPatterns {α : Type*} {n : ℕ} {A : Set (Fin n → α)}
    {x : Fin n → α} {u : Pattern n} :
    u ∈ mismatchPatterns A x ↔ ∃ y ∈ A, ∀ i, u i = false → x i = y i := by
  classical
  simp [mismatchPatterns]

lemma mismatchPatterns_nonempty {α : Type*} {n : ℕ} {A : Set (Fin n → α)}
    (hA : A.Nonempty) (x : Fin n → α) : (mismatchPatterns A x).Nonempty := by
  obtain ⟨y,hy⟩ := hA
  exact ⟨fun _ => true, mem_mismatchPatterns.mpr ⟨y,hy,by simp⟩⟩

lemma mismatchPatterns_mono {α : Type*} {n : ℕ} {A B : Set (Fin n → α)}
    (hAB : A ⊆ B) (x : Fin n → α) : mismatchPatterns A x ⊆ mismatchPatterns B x := by
  intro u hu
  obtain ⟨y,hy,hm⟩ := mem_mismatchPatterns.mp hu
  exact mem_mismatchPatterns.mpr ⟨y,hAB hy,hm⟩

noncomputable def convexDistanceSq {α : Type*} {n : ℕ}
    (A : Set (Fin n → α)) (x : Fin n → α) : ℝ := patternDistance (mismatchPatterns A x)

lemma convexDistanceSq_nonneg {α : Type*} {n : ℕ} (A : Set (Fin n → α)) (x : Fin n → α) :
    0 ≤ convexDistanceSq A x := patternDistance_nonneg _

lemma convexDistanceSq_le_dimension {α : Type*} {n : ℕ} (A : Set (Fin n → α)) (x : Fin n → α) :
    convexDistanceSq A x ≤ n := patternDistance_le_dimension _

lemma convexDistanceSq_zero {α : Type*} {n : ℕ} {A : Set (Fin n → α)}
    {x : Fin n → α} (hx : x ∈ A) : convexDistanceSq A x = 0 := by
  have hu : (fun _ => false) ∈ mismatchPatterns A x :=
    mem_mismatchPatterns.mpr ⟨x,hx,by simp⟩
  have hd := patternDistance_le (mismatchPatterns_nonempty ⟨x,hx⟩ x)
    (subset_convexHull ℝ _ ⟨fun _ => false,hu,rfl⟩)
  have he : sqNorm (bitVector (fun _ : Fin n => false)) = 0 := by simp [sqNorm,bitVector]
  rw [he] at hd
  exact le_antisymm hd (convexDistanceSq_nonneg _ _)

lemma convexDistance_weight_witness {α : Type*} [DecidableEq α] {n : ℕ} {A : Set (Fin n → α)}
    (hA : A.Nonempty) (x : Fin n → α) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ y ∈ A, (∑ i, if x i = y i then 0 else a i) ≤
      Real.sqrt (sqNorm a)*Real.sqrt (convexDistanceSq A x) := by
  classical
  obtain ⟨u,hu,hw⟩ := pattern_weight_witness (mismatchPatterns_nonempty hA x) a
  obtain ⟨y,hy,hm⟩ := mem_mismatchPatterns.mp hu
  refine ⟨y,hy,le_trans ?_ hw⟩
  apply Finset.sum_le_sum
  intro i _
  by_cases he : x i = y i
  · simp only [he,ite_true]
    exact mul_nonneg (ha i) (by cases h : u i <;> simp [bitVector,h])
  · have hb : u i = true := by cases h : u i <;> simp_all
    simp [he,bitVector,hb]

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal BigOperators
namespace TalagrandConc.Assignment.ACFresh

lemma continuous_optCost (N : ℕ) : Continuous (@optCost N) := by
  unfold optCost
  apply Continuous.finset_inf'_apply
  intro τ _
  unfold assignmentCost
  fun_prop

noncomputable def cappedObservable (N : ℕ) (b : ℝ) (x : Fin (N*N) → unitInterval) : ℝ :=
  optCost (cappedCosts b (cubeLift N x))
noncomputable def originalObservable (N : ℕ) (x : Fin (N*N) → unitInterval) : ℝ :=
  optCost (cubeLift N x)

lemma continuous_cappedObservable (N : ℕ) (b : ℝ) : Continuous (cappedObservable N b) := by
  apply (continuous_optCost N).comp
  unfold cappedCosts cubeLift
  fun_prop
lemma continuous_originalObservable (N : ℕ) : Continuous (originalObservable N) :=
  (continuous_optCost N).comp (continuous_cubeLift N)

noncomputable def assignmentWeights {N : ℕ} (τ : Equiv.Perm (Fin N)) : Fin (N*N) → ℝ :=
  fun k => if (edgeEquiv N k).2=τ (edgeEquiv N k).1 then 1 else 0

lemma assignmentWeights_nonneg {N : ℕ} (τ : Equiv.Perm (Fin N)) :
    ∀ k, 0 ≤ assignmentWeights τ k := by
  intro k
  unfold assignmentWeights
  split_ifs <;> norm_num

lemma assignmentWeights_norm {N : ℕ} (τ : Equiv.Perm (Fin N)) : sqNorm (assignmentWeights τ)=N := by
  unfold sqNorm assignmentWeights
  rw [← (edgeEquiv N).symm.sum_comp]
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type]
  simp

lemma assignmentWeights_mismatch {N : ℕ} (τ : Equiv.Perm (Fin N))
    (x y : Fin (N*N) → unitInterval) :
    (∑ k, if x k=y k then 0 else assignmentWeights τ k)=
      ∑ i, if x ((edgeEquiv N).symm (i,τ i))=y ((edgeEquiv N).symm (i,τ i)) then 0 else 1 := by
  classical
  unfold assignmentWeights
  rw [← (edgeEquiv N).symm.sum_comp]
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (τ i)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

lemma cappedObservable_gap {N : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (x : Fin (N*N) → unitInterval) : ∃ τ : Equiv.Perm (Fin N),
    ∀ y : Fin (N*N) → unitInterval, cappedObservable N b y-cappedObservable N b x ≤
      b * (∑ k, if x k=y k then 0 else assignmentWeights τ k) := by
  classical
  obtain ⟨τ,hτ,_⟩ := exists_optimal_assignment (cappedCosts b (cubeLift N x))
  refine ⟨τ,fun y => ?_⟩
  have hy := optCost_le_assignmentCost (cappedCosts b (cubeLift N y)) τ
  change cappedObservable N b y ≤ assignmentCost (cappedCosts b (cubeLift N y)) τ at hy
  have hx : cappedObservable N b x=assignmentCost (cappedCosts b (cubeLift N x)) τ := hτ.symm
  rw [hx,assignmentWeights_mismatch,Finset.mul_sum]
  apply (sub_le_sub_right hy _).trans
  rw [assignmentCost,assignmentCost,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  let k := (edgeEquiv N).symm (i,τ i)
  change min (y k:ℝ) b-min (x k:ℝ) b ≤ b*(if x k=y k then 0 else 1)
  by_cases h : x k=y k
  · simp [h]
  · rw [if_neg h,mul_one]
    have hl : 0 ≤ min (x k:ℝ) b := le_min (x k).property.1 hb
    have hu : min (y k:ℝ) b ≤ b := min_le_right _ _
    linarith

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal
namespace TalagrandConc.Assignment.ACFresh

lemma originalObservable_median {N : ℕ} {M : ℝ}
    (hM : TalagrandConc.BinPacking.IsMedian (costLaw N) optCost M) :
    TalagrandConc.BinPacking.IsMedian (cubeLaw (N*N)) (originalObservable N) M := by
  have hlo : MeasurableSet {X : Fin N × Fin N → ℝ | optCost X ≤ M} :=
    measurableSet_le (continuous_optCost N).measurable measurable_const
  have hhi : MeasurableSet {X : Fin N × Fin N → ℝ | M ≤ optCost X} :=
    measurableSet_le measurable_const (continuous_optCost N).measurable
  constructor
  · have h := hM.1
    rw [← (cubeLift_preserving N).map_eq,Measure.map_apply (cubeLift_preserving N).measurable hlo] at h
    exact h
  · have h := hM.2
    rw [← (cubeLift_preserving N).map_eq,Measure.map_apply (cubeLift_preserving N).measurable hhi] at h
    exact h

lemma cappedObservable_le_original (N : ℕ) (b : ℝ) (x : Fin (N*N) → unitInterval) :
    cappedObservable N b x ≤ originalObservable N x := capped_optCost_le _ _

lemma capped_quantiles {N : ℕ} {M b : ℝ}
    (hM : TalagrandConc.BinPacking.IsMedian (costLaw N) optCost M)
    {E : Set (Fin (N*N) → unitInterval)} (hE : cubeLaw (N*N) E ≤ (1/4:ENNReal))
    (heq : ∀ x ∉ E, cappedObservable N b x=originalObservable N x) :
    (1/2:ENNReal) ≤ cubeLaw (N*N) {x | cappedObservable N b x ≤ M} ∧
    (1/4:ENNReal) ≤ cubeLaw (N*N) {x | M ≤ cappedObservable N b x} := by
  have hm := originalObservable_median hM
  constructor
  · exact hm.1.trans (measure_mono (fun x hx => (cappedObservable_le_original N b x).trans hx))
  · have hsub : {x | M ≤ originalObservable N x} ⊆ E ∪ {x | M ≤ cappedObservable N b x} := by
      intro x hx
      by_cases he : x ∈ E
      · exact Or.inl he
      · exact Or.inr (by change M ≤ cappedObservable N b x; rw [heq x he]; exact hx)
    have h := hm.2.trans ((measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add_left hE _)))
    by_contra hn
    have hlt : cubeLaw (N*N) {x | M ≤ cappedObservable N b x} < (1/4:ENNReal) := lt_of_not_ge hn
    have hh : (1/4:ENNReal)+cubeLaw (N*N) {x | M ≤ cappedObservable N b x} < 1/2 := by
      calc
        _ < (1/4:ENNReal)+1/4 := ENNReal.add_lt_add_left (by norm_num) hlt
        _ = ENNReal.ofReal ((1/4:ℝ)+1/4) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num [ENNReal.ofReal_div_of_pos]
        _ = 1/2 := by norm_num [ENNReal.ofReal_div_of_pos]
    exact (not_lt_of_ge h) hh

lemma optCost_bounds {N : ℕ} (X : Fin N × Fin N → ℝ)
    (hX : ∀ p, X p ∈ Set.Icc (0:ℝ) 1) : 0 ≤ optCost X ∧ optCost X ≤ N := by
  obtain ⟨τ,hτ,_⟩ := exists_optimal_assignment X
  rw [← hτ]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (hX (i,τ i)).1)
  · calc
      assignmentCost X τ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => (hX (i,τ i)).2)
      _ = N := by simp

lemma originalObservable_bounds (N : ℕ) (x : Fin (N*N) → unitInterval) :
    0 ≤ originalObservable N x ∧ originalObservable N x ≤ N :=
  optCost_bounds _ (fun p => (x ((edgeEquiv N).symm p)).property)

lemma native_median_bounds {N : ℕ} {M : ℝ}
    (hM : TalagrandConc.BinPacking.IsMedian (costLaw N) optCost M) : 0 ≤ M ∧ M ≤ N := by
  have hm := originalObservable_median hM
  constructor
  · by_contra h
    have he : {x | originalObservable N x ≤ M} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact not_le_of_gt ((lt_of_not_ge h).trans_le (originalObservable_bounds N x).1)
    unfold TalagrandConc.BinPacking.IsMedian at hm
    rw [he,measure_empty] at hm
    norm_num at hm
  · by_contra h
    have he : {x | M ≤ originalObservable N x} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact not_le_of_gt ((originalObservable_bounds N x).2.trans_lt (lt_of_not_ge h))
    unfold TalagrandConc.BinPacking.IsMedian at hm
    rw [he,measure_empty] at hm
    norm_num at hm

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal
namespace TalagrandConc.Assignment.ACFresh

lemma native_tail_eq_cube (N : ℕ) (M w : ℝ) :
    costLaw N {X | w ≤ |optCost X-M|}=
      cubeLaw (N*N) {x | w ≤ |originalObservable N x-M|} := by
  rw [← (cubeLift_preserving N).map_eq]
  apply Measure.map_apply (cubeLift_preserving N).measurable
  exact measurableSet_le measurable_const (((continuous_optCost N).sub continuous_const).abs.measurable)

lemma native_tail_le_capped {N : ℕ} (M w b : ℝ)
    {E : Set (Fin (N*N) → unitInterval)}
    (heq : ∀ x ∉ E, cappedObservable N b x=originalObservable N x) :
    costLaw N {X | w ≤ |optCost X-M|} ≤ cubeLaw (N*N) E+
      cubeLaw (N*N) {x | w ≤ |cappedObservable N b x-M|} := by
  rw [native_tail_eq_cube]
  apply (measure_mono (show {x | w ≤ |originalObservable N x-M|} ⊆
    E ∪ {x | w ≤ |cappedObservable N b x-M|} from ?_)).trans (measure_union_le _ _)
  intro x hx
  by_cases he : x ∈ E
  · exact Or.inl he
  · right
    change w ≤ |cappedObservable N b x-M|
    rw [heq x he]
    exact hx

lemma native_tail_zero_of_range {N : ℕ} {M w : ℝ}
    (hM : TalagrandConc.BinPacking.IsMedian (costLaw N) optCost M) (hw : (N:ℝ) < w) :
    costLaw N {X | w ≤ |optCost X-M|}=0 := by
  rw [native_tail_eq_cube]
  have hm := native_median_bounds hM
  have he : {x | w ≤ |originalObservable N x-M|}=∅ := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    have hx := originalObservable_bounds N x
    have hb : |originalObservable N x-M| ≤ N := abs_le.mpr ⟨by linarith,by linarith⟩
    exact not_le_of_gt (hb.trans_lt hw)
  rw [he,measure_empty]

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment.ACFresh

noncomputable def clampedCell (m : ℕ) (t : ℝ) : ℕ := min (Nat.floor t) (m-1)

theorem clampedCell_lt (m : ℕ) (hm : 0 < m) (t : ℝ) : clampedCell m t < m := by
  unfold clampedCell
  exact (min_le_right _ _).trans_lt (by omega)

theorem clampedCell_bounds (m : ℕ) (hm : 0 < m) (t : ℝ)
    (ht0 : 0 ≤ t) (htm : t ≤ m) :
    (clampedCell m t : ℝ) ≤ t ∧ t ≤ (clampedCell m t : ℝ)+1 := by
  constructor
  · exact (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le ht0)
  · unfold clampedCell
    by_cases h : Nat.floor t ≤ m-1
    · rw [min_eq_left h]
      exact (Nat.lt_floor_add_one t).le
    · rw [min_eq_right (by omega)]
      have he : ((m-1:ℕ):ℝ)+1=(m:ℝ) := by
        exact_mod_cast (show m-1+1=m by omega)
      rwa [he]

theorem dyadicSide_eq_inv (k : ℕ) : (2:ℝ)^(-(k:ℤ))=((2:ℝ)^k)⁻¹ := by
  rw [zpow_neg,zpow_natCast]

theorem dyadicSide_pos (k : ℕ) : 0 < (2:ℝ)^(-(k:ℤ)) := by positivity

theorem dyadicSide_mul (k : ℕ) : (2:ℝ)^k*(2:ℝ)^(-(k:ℤ))=1 := by
  rw [dyadicSide_eq_inv]
  exact mul_inv_cancel₀ (by positivity)

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment.ACFresh

theorem clampedCell_eq_iff {m j : ℕ} (_hm : 0 < m) (hj : j < m)
    (t : ℝ) (ht0 : 0 ≤ t) (_htm : t ≤ m) :
    clampedCell m t=j ↔ (j:ℝ) ≤ t ∧ (j+1=m ∨ t < (j:ℝ)+1) := by
  unfold clampedCell
  constructor
  · intro h
    have hlow : j ≤ Nat.floor t := by rw [← h]; exact min_le_left _ _
    refine ⟨(Nat.cast_le.mpr hlow).trans (Nat.floor_le ht0),?_⟩
    by_cases he : j+1=m
    · exact Or.inl he
    · right
      have hfloor : Nat.floor t=j := by omega
      rw [← hfloor]
      exact Nat.lt_floor_add_one t
  · rintro ⟨hlo,hhi⟩
    have hfloor : j ≤ Nat.floor t := Nat.le_floor hlo
    rcases hhi with he | hhi
    · have hpred : m-1=j := by omega
      rw [hpred,min_eq_right hfloor]
    · have heq : Nat.floor t=j := (Nat.floor_eq_iff ht0).mpr ⟨hlo,hhi⟩
      rw [heq,min_eq_left (by omega)]

theorem clampedCell_eq_of_open {m j : ℕ} (hj : j < m) (t : ℝ)
    (ht : (j:ℝ) ≤ t) (ht' : t < (j:ℝ)+1) : clampedCell m t=j := by
  unfold clampedCell
  have h0 : 0 ≤ t := (Nat.cast_nonneg j).trans ht
  rw [(Nat.floor_eq_iff h0).mpr ⟨ht,ht'⟩,min_eq_left (by omega)]

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

noncomputable def matchError {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (x : Fin n → X) (u : Pattern n) (y : Fin n → X) : ℝ :=
  ∑ i, if u i = false then dist (x i) (y i) else 0

lemma matchError_nonneg {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (x : Fin n → X) (u : Pattern n) (y : Fin n → X) : 0 ≤ matchError x u y := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

lemma continuous_matchError {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (x : Fin n → X) (u : Pattern n) : Continuous (matchError x u) := by
  unfold matchError
  apply continuous_finsetSum
  intro i _
  by_cases h : u i = false
  · simp only [h,ite_true]
    fun_prop
  · have ht : u i = true := Bool.eq_true_of_not_eq_false h
    simp only [ht, Bool.true_eq_false, ↓reduceIte]
    exact continuous_const

lemma matchError_zero_iff {X : Type*} [MetricSpace X] {n : ℕ}
    (x : Fin n → X) (u : Pattern n) (y : Fin n → X) :
    matchError x u y = 0 ↔ ∀ i, u i = false → x i = y i := by
  constructor
  · intro h i hi
    have hb : dist (x i) (y i) ≤ matchError x u y := by
      have hs := Finset.single_le_sum (f := fun j => if u j = false then dist (x j) (y j) else 0)
        (s := Finset.univ) (a := i) (by intro j _; split_ifs <;> positivity) (Finset.mem_univ i)
      change dist (x i) (y i) ≤ ∑ j, if u j = false then dist (x j) (y j) else 0
      simpa only [hi,ite_true] using hs
    rw [h] at hb
    exact dist_le_zero.mp hb
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · simp [h i hi]
    · rfl

lemma matchError_quantized_bound {X Y : Type*} [PseudoMetricSpace X] {n : ℕ}
    (q : X → Y) (δ : ℝ) (hδ : 0 ≤ δ)
    (hq : ∀ x y, q x=q y → dist x y ≤ δ)
    (x y : Fin n → X) (u : Pattern n) (hu : ∀ i, u i=false → q (x i)=q (y i)) :
    matchError x u y ≤ n*δ := by
  calc
    matchError x u y ≤ ∑ _i : Fin n, δ := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact hq _ _ (hu i hi)
      · exact hδ
    _ = n*δ := by simp

lemma compact_matchError_positive {X : Type*} [MetricSpace X] {n : ℕ}
    {A : Set (Fin n → X)} (hA : IsCompact A) (hne : A.Nonempty)
    (x : Fin n → X) (u : Pattern n) (hu : u ∉ mismatchPatterns A x) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ A, c ≤ matchError x u y := by
  obtain ⟨y,hy,hm⟩ := hA.exists_isMinOn hne (continuous_matchError x u).continuousOn
  refine ⟨matchError x u y,?_,hm⟩
  apply lt_of_le_of_ne (matchError_nonneg x u y)
  intro he
  apply hu
  exact mem_mismatchPatterns.mpr ⟨y,hy,(matchError_zero_iff x u y).mp he.symm⟩

end TalagrandConc.Assignment.ACFresh
end

section

open Filter
open scoped Topology

namespace TalagrandConc.Assignment.ACFresh

def quantizedPoint {X Y : Type*} {n : ℕ} (q : X → Y) (x : Fin n → X) : Fin n → Y :=
  fun i => q (x i)

def quantizedSet {X Y : Type*} {n : ℕ} (q : X → Y) (A : Set (Fin n → X)) :
    Set (Fin n → Y) := quantizedPoint q '' A

lemma exact_pattern_quantized {X Y : Type*} {n : ℕ} (q : X → Y)
    {A : Set (Fin n → X)} {x : Fin n → X} {u : Pattern n}
    (hu : u ∈ mismatchPatterns A x) :
    u ∈ mismatchPatterns (quantizedSet q A) (quantizedPoint q x) := by
  obtain ⟨y,hy,hm⟩ := mem_mismatchPatterns.mp hu
  exact mem_mismatchPatterns.mpr ⟨quantizedPoint q y,⟨y,hy,rfl⟩,
    fun i hi => congrArg q (hm i hi)⟩

lemma quantized_pattern_error {X Y : Type*} [PseudoMetricSpace X] {n : ℕ}
    (q : X → Y) {δ : ℝ} (hδ : 0 ≤ δ) (hq : ∀ x y, q x=q y → dist x y ≤ δ)
    {A : Set (Fin n → X)} {x : Fin n → X} {u : Pattern n}
    (hu : u ∈ mismatchPatterns (quantizedSet q A) (quantizedPoint q x)) :
    ∃ y ∈ A, matchError x u y ≤ n*δ := by
  obtain ⟨z,⟨y,hy,rfl⟩,hm⟩ := mem_mismatchPatterns.mp hu
  exact ⟨y,hy,matchError_quantized_bound q δ hδ hq x y u hm⟩

lemma compact_patterns_eventually_equal {X : Type*} [MetricSpace X] {Y : ℕ → Type*}
    {n : ℕ} {A : Set (Fin n → X)} (hA : IsCompact A) (hne : A.Nonempty)
    (q : (m : ℕ) → X → Y m) (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m)
    (hq : ∀ m x y, q m x=q m y → dist x y ≤ δ m)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : Fin n → X) :
    ∀ᶠ m in atTop, mismatchPatterns (quantizedSet (q m) A) (quantizedPoint (q m) x) =
      mismatchPatterns A x := by
  classical
  have hu (u : Pattern n) : ∀ᶠ m in atTop,
      (u ∈ mismatchPatterns (quantizedSet (q m) A) (quantizedPoint (q m) x) ↔
        u ∈ mismatchPatterns A x) := by
    by_cases hex : u ∈ mismatchPatterns A x
    · exact Filter.Eventually.of_forall fun m => ⟨fun _ => hex,fun _ => exact_pattern_quantized (q m) hex⟩
    · obtain ⟨c,hc,hmin⟩ := compact_matchError_positive hA hne x u hex
      have ht : Tendsto (fun m => (n:ℝ)*δ m) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.mul hlim
      have hev := ht.eventually_lt_const hc
      filter_upwards [hev] with m hm
      constructor
      · intro hmem
        obtain ⟨y,hy,hb⟩ := quantized_pattern_error (q m) (hδ m) (hq m) hmem
        exact False.elim ((not_lt_of_ge ((hmin y hy).trans hb)) hm)
      · exact fun he => False.elim (hex he)
  have hall : ∀ᶠ m in atTop, ∀ u : Pattern n,
      (u ∈ mismatchPatterns (quantizedSet (q m) A) (quantizedPoint (q m) x) ↔
        u ∈ mismatchPatterns A x) := Filter.eventually_all.mpr hu
  filter_upwards [hall] with m hm
  exact Finset.ext hm

lemma compact_distance_eventually_equal {X : Type*} [MetricSpace X] {Y : ℕ → Type*}
    {n : ℕ} {A : Set (Fin n → X)} (hA : IsCompact A) (hne : A.Nonempty)
    (q : (m : ℕ) → X → Y m) (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m)
    (hq : ∀ m x y, q m x=q m y → dist x y ≤ δ m)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : Fin n → X) :
    ∀ᶠ m in atTop, convexDistanceSq (quantizedSet (q m) A) (quantizedPoint (q m) x) =
      convexDistanceSq A x := by
  filter_upwards [compact_patterns_eventually_equal hA hne q δ hδ hq hlim x] with m hm
  exact congrArg patternDistance hm

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal BigOperators
namespace TalagrandConc.Assignment.ACFresh

lemma cube_quantized_fiber {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : unitInterval → Y) (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y)
    (hatom : ∀ y, (volume : Measure unitInterval) {x | q x=y}=ENNReal.ofReal (p y))
    (n : ℕ) (y : Fin n → Y) :
    cubeLaw n {x | quantizedPoint q x=y}=ENNReal.ofReal (productWeight p n y) := by
  have he : {x | quantizedPoint q x=y}=Set.pi Set.univ (fun i => {x | q x=y i}) := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_pi,Set.mem_univ,true_implies]
    exact funext_iff
  rw [he]
  change (Measure.pi (fun _ : Fin n => (volume : Measure unitInterval))) _=_
  rw [Measure.pi_pi]
  simp only [hatom]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => hp (y i))).symm

lemma cube_quantized_mass {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : unitInterval → Y) (hq : Measurable q) (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y)
    (hatom : ∀ y, (volume : Measure unitInterval) {x | q x=y}=ENNReal.ofReal (p y))
    (n : ℕ) (B : Set (Fin n → Y)) :
    cubeLaw n (quantizedPoint q ⁻¹' B)=ENNReal.ofReal (productMass p n B) := by
  classical
  have hm : Measurable (quantizedPoint (n := n) q) := by
    apply measurable_pi_lambda
    intro i
    exact hq.comp (measurable_pi_apply i)
  have hsum := sum_measure_preimage_singleton (μ := cubeLaw n) B.toFinite.toFinset
    (f := quantizedPoint q) (fun y _ => hm (measurableSet_singleton y))
  simp only [Set.Finite.coe_toFinset] at hsum
  rw [← hsum]
  change (∑ y ∈ B.toFinite.toFinset, cubeLaw n {x | quantizedPoint q x=y})=_
  simp only [cube_quantized_fiber q p hp hatom]
  unfold productMass productMean finiteMean
  simp only [mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun x => x ∈ B)=B.toFinite.toFinset := by ext x; simp
  rw [he,ENNReal.ofReal_sum_of_nonneg (fun x _ => productWeight_nonneg hp n x)]

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal BigOperators Topology
namespace TalagrandConc.Assignment.ACFresh

noncomputable def intervalIndex (k : ℕ) (x : unitInterval) : Fin (2^k) :=
  ⟨clampedCell (2^k) ((2:ℝ)^k*(x:ℝ)), clampedCell_lt _ (by positivity) _⟩

noncomputable def cellLower (k : ℕ) (j : Fin (2^k)) : unitInterval :=
  ⟨(j.val:ℝ)/(2:ℝ)^k, by
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (2:ℝ)^k)).mpr
      exact_mod_cast j.isLt.le⟩
noncomputable def cellUpper (k : ℕ) (j : Fin (2^k)) : unitInterval :=
  ⟨((j.val:ℝ)+1)/(2:ℝ)^k, by
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (2:ℝ)^k)).mpr
      exact_mod_cast (show j.val+1 ≤ 2^k from j.isLt)⟩

lemma cell_width (k : ℕ) (j : Fin (2^k)) :
    (cellUpper k j:ℝ)-(cellLower k j:ℝ)=(2:ℝ)^(-(k:ℤ)) := by
  change ((j.val:ℝ)+1)/(2:ℝ)^k-(j.val:ℝ)/(2:ℝ)^k=_
  rw [dyadicSide_eq_inv]
  ring

lemma intervalIndex_bounds (k : ℕ) (x : unitInterval) :
    x ∈ Set.Icc (cellLower k (intervalIndex k x)) (cellUpper k (intervalIndex k x)) := by
  have hp : 0 < (2:ℝ)^k := by positivity
  have hb := clampedCell_bounds (2^k) (by positivity) ((2:ℝ)^k*(x:ℝ))
    (mul_nonneg hp.le x.property.1) (by simpa only [Nat.cast_pow,Nat.cast_ofNat,mul_one] using (mul_le_mul_of_nonneg_left x.property.2 hp.le))
  constructor
  · change (clampedCell (2^k) ((2:ℝ)^k*(x:ℝ)):ℝ)/(2:ℝ)^k ≤ (x:ℝ)
    exact (div_le_iff₀ hp).mpr (by nlinarith [hb.1])
  · change (x:ℝ) ≤ ((clampedCell (2^k) ((2:ℝ)^k*(x:ℝ)):ℝ)+1)/(2:ℝ)^k
    exact (le_div_iff₀ hp).mpr (by nlinarith [hb.2])

lemma intervalIndex_open (k : ℕ) (j : Fin (2^k)) :
    Set.Ioo (cellLower k j) (cellUpper k j) ⊆ {x | intervalIndex k x=j} := by
  intro x hx
  apply Fin.ext
  change clampedCell (2^k) ((2:ℝ)^k*(x:ℝ))=j.val
  apply clampedCell_eq_of_open j.isLt
  · have h := (div_lt_iff₀ (by positivity : 0 < (2:ℝ)^k)).mp hx.1
    nlinarith
  · have h := (lt_div_iff₀ (by positivity : 0 < (2:ℝ)^k)).mp hx.2
    nlinarith

lemma intervalIndex_atom (k : ℕ) (j : Fin (2^k)) :
    (volume : Measure unitInterval) {x | intervalIndex k x=j}=
      ENNReal.ofReal ((2:ℝ)^(-(k:ℤ))) := by
  apply le_antisymm
  · calc
      volume {x | intervalIndex k x=j} ≤ volume (Set.Icc (cellLower k j) (cellUpper k j)) :=
        measure_mono (fun x hx => by rw [← hx]; exact intervalIndex_bounds k x)
      _ = _ := by rw [unitInterval.volume_Icc,cell_width]
  · calc
      _ = volume (Set.Ioo (cellLower k j) (cellUpper k j)) := by
        rw [unitInterval.volume_Ioo,cell_width]
      _ ≤ _ := measure_mono (intervalIndex_open k j)

lemma measurable_intervalIndex (k : ℕ) : Measurable (intervalIndex k) := by
  have he : intervalIndex k = fun x : unitInterval => Fin.ofNat (2^k) (clampedCell (2^k) ((2:ℝ)^k*(x:ℝ))) := by
    funext x
    apply Fin.ext
    simp only [intervalIndex,Fin.val_ofNat]
    exact (Nat.mod_eq_of_lt (clampedCell_lt (2^k) (by positivity) ((2:ℝ)^k*(x:ℝ)))).symm
  rw [he]
  apply (measurable_of_countable (Fin.ofNat (2^k))).comp
  unfold clampedCell
  exact (Nat.measurable_floor.comp (by fun_prop)).min measurable_const

lemma dist_same_intervalIndex {k : ℕ} {x y : unitInterval}
    (h : intervalIndex k x=intervalIndex k y) : dist x y ≤ (2:ℝ)^(-(k:ℤ)) := by
  have hx := intervalIndex_bounds k x
  have hy := intervalIndex_bounds k y
  rw [← h] at hy
  rw [Subtype.dist_eq,Real.dist_eq,abs_le]
  have hw := cell_width k (intervalIndex k x)
  change (cellLower k (intervalIndex k x):ℝ) ≤ (x:ℝ) ∧
    (x:ℝ) ≤ (cellUpper k (intervalIndex k x):ℝ) at hx
  change (cellLower k (intervalIndex k x):ℝ) ≤ (y:ℝ) ∧
    (y:ℝ) ≤ (cellUpper k (intervalIndex k x):ℝ) at hy
  constructor <;> linarith

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma snoc_real_mix {n : ℕ} (x y : Fin n → ℝ) (b s t : ℝ) (hst : s+t=1) :
    Fin.snoc (s • x+t • y) b = s • Fin.snoc x b+t • Fin.snoc y b := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun z : ℝ => z*b) hst]
  · simp

lemma bitVector_snoc {n : ℕ} (u : Pattern n) (b : Bool) :
    bitVector (Fin.snoc u b) = Fin.snoc (bitVector u) (if b then 1 else 0) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [bitVector]

lemma snoc_mem_patternHull {n : ℕ} {U : Finset (Pattern n)}
    {V : Finset (Pattern (n+1))} (b : Bool)
    (hUV : ∀ u ∈ U, Fin.snoc u b ∈ V) {v : Fin n → ℝ} (hv : v ∈ patternHull U) :
    Fin.snoc v (if b then 1 else 0) ∈ patternHull V := by
  have hc : Convex ℝ {w : Fin n → ℝ | Fin.snoc w (if b then 1 else 0) ∈ patternHull V} := by
    intro x hx y hy s t hs ht hst
    change Fin.snoc (s • x+t • y) (if b then 1 else 0) ∈ patternHull V
    rw [snoc_real_mix _ _ _ _ _ hst]
    exact (convex_convexHull ℝ _) hx hy hs ht hst
  apply (convexHull_min ?_ hc) hv
  rintro _ ⟨u,hu,rfl⟩
  change Fin.snoc (bitVector u) (if b then 1 else 0) ∈ patternHull V
  rw [← bitVector_snoc]
  exact subset_convexHull ℝ _ ⟨Fin.snoc u b,hUV u hu,rfl⟩

lemma sqNorm_snoc {n : ℕ} (v : Fin n → ℝ) (b : ℝ) :
    sqNorm (Fin.snoc v b) = sqNorm v+b^2 := by
  simp [sqNorm,Fin.sum_univ_castSucc]

lemma sqNorm_mix_le {n : ℕ} (x y : Fin n → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1) :
    sqNorm (s • x+t • y) ≤ s*sqNorm x+t*sqNorm y := by
  simp only [sqNorm,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have he : s*(x i)^2+t*(y i)^2-(s*x i+t*y i)^2 = s*t*(x i-y i)^2 := by
    have ht' : t=1-s := by linarith
    rw [ht']
    ring
  have hpos := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x i-y i))
  linarith

lemma patternDistance_snoc_mix {n : ℕ} {U W : Finset (Pattern n)}
    {V : Finset (Pattern (n+1))} (hU : U.Nonempty) (hW : W.Nonempty)
    (h0 : ∀ u ∈ U, Fin.snoc u false ∈ V) (h1 : ∀ u ∈ W, Fin.snoc u true ∈ V)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    patternDistance V ≤ (1-t)^2+t*patternDistance U+(1-t)*patternDistance W := by
  let x := patternMin U hU
  let y := patternMin W hW
  have hx := snoc_mem_patternHull false h0 (patternMin_spec U hU).1
  have hy := snoc_mem_patternHull true h1 (patternMin_spec W hW).1
  simp only [Bool.false_eq_true,ite_false,ite_true] at hx hy
  have hv : V.Nonempty := by
    obtain ⟨u,hu⟩ := hU
    exact ⟨Fin.snoc u false,h0 u hu⟩
  have hm := (convex_convexHull ℝ (bitVector '' (V : Set (Pattern (n+1)))))
    hx hy ht (sub_nonneg.mpr ht1) (by ring)
  have he : t • Fin.snoc x 0+(1-t) • Fin.snoc y 1 = Fin.snoc (t • x+(1-t) • y) (1-t) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  change t • Fin.snoc x 0+(1-t) • Fin.snoc y 1 ∈ patternHull V at hm
  rw [he] at hm
  have hb := patternDistance_le hv hm
  rw [sqNorm_snoc] at hb
  have hc := sqNorm_mix_le x y ht (sub_nonneg.mpr ht1) (by ring)
  rw [patternDistance_eq hU,patternDistance_eq hW]
  dsimp [x,y] at hb hc
  linarith

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment.ACFresh

def lastFiber {α : Type*} {n : ℕ} (A : Set (Fin (n+1) → α)) (a : α) : Set (Fin n → α) :=
  {x | Fin.snoc x a ∈ A}

def lastProjection {α : Type*} {n : ℕ} (A : Set (Fin (n+1) → α)) : Set (Fin n → α) :=
  {x | ∃ a, Fin.snoc x a ∈ A}

lemma lastFiber_subset {α : Type*} {n : ℕ} (A : Set (Fin (n+1) → α)) (a : α) :
    lastFiber A a ⊆ lastProjection A := fun _ hx => ⟨a,hx⟩

lemma lastProjection_nonempty {α : Type*} {n : ℕ} {A : Set (Fin (n+1) → α)}
    (hA : A.Nonempty) : (lastProjection A).Nonempty := by
  obtain ⟨x,hx⟩ := hA
  refine ⟨Fin.init x,x (Fin.last n),?_⟩
  simpa using hx

lemma fiber_pattern_snoc {α : Type*} {n : ℕ} {A : Set (Fin (n+1) → α)}
    (a : α) (x : Fin n → α) {u : Pattern n} (hu : u ∈ mismatchPatterns (lastFiber A a) x) :
    Fin.snoc u false ∈ mismatchPatterns A (Fin.snoc x a) := by
  obtain ⟨y,hy,hm⟩ := mem_mismatchPatterns.mp hu
  apply mem_mismatchPatterns.mpr
  refine ⟨Fin.snoc y a,hy,?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa using hm j

lemma projection_pattern_snoc {α : Type*} {n : ℕ} {A : Set (Fin (n+1) → α)}
    (a : α) (x : Fin n → α) {u : Pattern n} (hu : u ∈ mismatchPatterns (lastProjection A) x) :
    Fin.snoc u true ∈ mismatchPatterns A (Fin.snoc x a) := by
  obtain ⟨y,⟨b,hy⟩,hm⟩ := mem_mismatchPatterns.mp hu
  apply mem_mismatchPatterns.mpr
  refine ⟨Fin.snoc y b,hy,?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa using hm j

lemma convexDistanceSq_snoc_mix {α : Type*} {n : ℕ} {A : Set (Fin (n+1) → α)}
    (a : α) (x : Fin n → α) (hf : (lastFiber A a).Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    convexDistanceSq A (Fin.snoc x a) ≤ (1-t)^2+t*convexDistanceSq (lastFiber A a) x+
      (1-t)*convexDistanceSq (lastProjection A) x := by
  exact patternDistance_snoc_mix (mismatchPatterns_nonempty hf x)
    (mismatchPatterns_nonempty (hf.mono (lastFiber_subset A a)) x)
    (fun u hu => fiber_pattern_snoc a x hu) (fun u hu => projection_pattern_snoc a x hu) ht ht1

lemma convexDistanceSq_snoc_projection {α : Type*} {n : ℕ} {A : Set (Fin (n+1) → α)}
    (hA : A.Nonempty) (a : α) (x : Fin n → α) :
    convexDistanceSq A (Fin.snoc x a) ≤ 1+convexDistanceSq (lastProjection A) x := by
  let W := mismatchPatterns (lastProjection A) x
  have hW : W.Nonempty := mismatchPatterns_nonempty (lastProjection_nonempty hA) x
  have hm := snoc_mem_patternHull true (fun u hu => projection_pattern_snoc a x hu)
    (patternMin_spec W hW).1
  simp only [ite_true] at hm
  have hb := patternDistance_le (mismatchPatterns_nonempty hA (Fin.snoc x a)) hm
  rw [sqNorm_snoc,one_pow] at hb
  change patternDistance _ ≤ 1+patternDistance W
  rw [patternDistance_eq hW]
  linarith

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma productMass_empty {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ) :
    productMass p n ∅ = 0 := by
  simp [productMass,productMean,finiteMean]

lemma productMass_pos_nonempty {α : Type*} [Fintype α] {p : α → ℝ}
    {n : ℕ} {A : Set (Fin n → α)} (h : 0 < productMass p n A) : A.Nonempty := by
  by_contra hn
  have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  rw [he,productMass_empty] at h
  exact (lt_irrefl 0) h

lemma productMass_le_one {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (n : ℕ) (A : Set (Fin n → α)) :
    productMass p n A ≤ 1 := by
  classical
  calc
    productMass p n A ≤ finiteMean (productWeight p n) (fun _ => 1) := by
      apply finiteMean_mono (productWeight_nonneg hp n)
      intro x
      split_ifs <;> norm_num
    _ = 1 := finiteMean_const (productWeight_sum hs n) 1

lemma productMass_succ {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ)
    (A : Set (Fin (n+1) → α)) :
    productMass p (n+1) A = finiteMean p (fun a => productMass p n (lastFiber A a)) := by
  classical
  simp only [productMass,productMean_succ,lastFiber,Set.mem_ofPred_eq]
  rfl

lemma productMass_le_projection {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) {n : ℕ} (A : Set (Fin (n+1) → α)) :
    productMass p (n+1) A ≤ productMass p n (lastProjection A) := by
  rw [productMass_succ]
  calc
    finiteMean p (fun a => productMass p n (lastFiber A a)) ≤
        finiteMean p (fun _ => productMass p n (lastProjection A)) :=
      finiteMean_mono hp (fun a => productMass_mono hp (lastFiber_subset A a))
    _ = _ := finiteMean_const hs _

lemma productMean_const {α : Type*} [Fintype α] {p : α → ℝ}
    (hs : ∑ a, p a = 1) (n : ℕ) (c : ℝ) : productMean p n (fun _ => c) = c :=
  finiteMean_const (productWeight_sum hs n) c

lemma productMean_mul_const {α : Type*} [Fintype α] (p : α → ℝ) (n : ℕ)
    (f : (Fin n → α) → ℝ) (c : ℝ) :
    productMean p n (fun x => f x*c) = productMean p n f*c :=
  finiteMean_mul_const _ _ _

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma exp_mix_le (a b t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (t*a+(1-t)*b) ≤ t*Real.exp a+(1-t)*Real.exp b := by
  simpa only [smul_eq_mul] using convexOn_exp.2
    (Set.mem_univ a) (Set.mem_univ b) ht (sub_nonneg.mpr ht1) (by ring)

lemma finiteMean_exp_sub {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ) (c : ℝ) :
    finiteMean w (fun a => Real.exp (f a-c)) =
      finiteMean w (fun a => Real.exp (f a)) / Real.exp c := by
  simp only [Real.exp_sub, div_eq_mul_inv]
  exact finiteMean_mul_const _ _ _

lemma finiteMean_exp_mix {Ω : Type*} [Fintype Ω] {w f g : Ω → ℝ}
    (hw : ∀ a, 0 ≤ w a) {A B t : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hf : finiteMean w (fun a => Real.exp (f a)) ≤ A)
    (hg : finiteMean w (fun a => Real.exp (g a)) ≤ B)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    finiteMean w (fun a => Real.exp (t*f a+(1-t)*g a)) ≤
      Real.exp (t*Real.log A+(1-t)*Real.log B) := by
  let c := t*Real.log A+(1-t)*Real.log B
  have hnormf : finiteMean w (fun a => Real.exp (f a-Real.log A)) ≤ 1 := by
    rw [finiteMean_exp_sub, Real.exp_log hA]
    exact (div_le_one hA).mpr hf
  have hnormg : finiteMean w (fun a => Real.exp (g a-Real.log B)) ≤ 1 := by
    rw [finiteMean_exp_sub, Real.exp_log hB]
    exact (div_le_one hB).mpr hg
  have hpoint (a : Ω) : Real.exp ((t*f a+(1-t)*g a)-c) ≤
      t*Real.exp (f a-Real.log A)+(1-t)*Real.exp (g a-Real.log B) := by
    convert exp_mix_le (f a-Real.log A) (g a-Real.log B) t ht ht1 using 1
    congr 1
    dsimp [c]
    ring
  have hm := finiteMean_mono hw hpoint
  rw [finiteMean_exp_sub] at hm
  have hid : finiteMean w (fun a => t*Real.exp (f a-Real.log A)+(1-t)*Real.exp (g a-Real.log B)) =
      t*finiteMean w (fun a => Real.exp (f a-Real.log A))+
      (1-t)*finiteMean w (fun a => Real.exp (g a-Real.log B)) := by
    simp only [finiteMean, mul_add, Finset.sum_add_distrib]
    congr 1 <;> rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [hid] at hm
  have hb : t*finiteMean w (fun a => Real.exp (f a-Real.log A))+
      (1-t)*finiteMean w (fun a => Real.exp (g a-Real.log B)) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hnormf ht,
      mul_le_mul_of_nonneg_left hnormg (sub_nonneg.mpr ht1)]
  exact (div_le_one (Real.exp_pos c)).mp (hm.trans hb)

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment.ACFresh

noncomputable def mixingLog (s : ℝ) : ℝ :=
  Real.log (1+s)+(1-2*s)*Real.log (1-s)-s^2

lemma mixingLog_deriv {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) (1/2)) :
    HasDerivAt mixingLog (1/(1+s)-2*Real.log (1-s)-(1-2*s)/(1-s)-2*s) s := by
  have hp : 0 < 1+s := by linarith [hs.1]
  have hm : 0 < 1-s := by linarith [hs.2]
  have h1 := ((hasDerivAt_const s (1:ℝ)).add (hasDerivAt_id s)).log hp.ne'
  have h2 := ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).log hm.ne'
  have h3 := ((hasDerivAt_const s (1:ℝ)).sub ((hasDerivAt_id s).const_mul 2)).mul h2
  apply ((h1.add h3).sub ((hasDerivAt_id s).pow 2)).congr_deriv
  dsimp
  ring

lemma mixingLog_nonneg {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) (1/2)) :
    0 ≤ mixingLog s := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/2)) := mixingLog_deriv hx
  have hc : ContinuousOn mixingLog (Set.Icc (0:ℝ) (1/2)) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm : MonotoneOn mixingLog (Set.Icc (0:ℝ) (1/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hd x hx').deriv]
      have hpos : 0 < 1-x := by linarith [hx'.2]
      have hp : 0 < 1+x := by linarith [hx'.1]
      have hl := Real.log_le_sub_one_of_pos hpos
      have hr : 0 ≤ 1/(1+x)-(1-2*x)/(1-x) := by
        apply (sub_nonneg.mpr ?_)
        apply (div_le_div_iff₀ hpos hp).mpr
        nlinarith [sq_nonneg x]
      linarith
  have h := hm (by norm_num) hs hs.1
  simpa [mixingLog] using h

lemma exp_quarter_le : Real.exp (1/4:ℝ) ≤ 3/2 := by
  have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ) < 1)
  norm_num at h ⊢
  linarith

lemma mixing_scalar {r : ℝ} (_hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      Real.exp ((1-t)^2/4-t*Real.log r) ≤ 2-r := by
  by_cases h : r ≤ 1/2
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    simp only [sub_zero, one_pow, zero_mul]
    exact exp_quarter_le.trans (by linarith)
  · have hs : 1-r ∈ Set.Icc (0:ℝ) (1/2) := ⟨by linarith, by linarith⟩
    have hm := mixingLog_nonneg hs
    have hlog : ((1-(2*r-1))^2/4-(2*r-1)*Real.log r) ≤ Real.log (2-r) := by
      dsimp [mixingLog] at hm
      have h1 : 1+(1-r)=2-r := by ring
      have h2 : 1-(1-r)=r := by ring
      rw [h1,h2] at hm
      nlinarith
    refine ⟨2*r-1, by linarith, by linarith, ?_⟩
    exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (by linarith))

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma reciprocal_mix_identity {c b : ℝ} (hc : 0 < c) (hb : 0 < b) (t : ℝ) :
    Real.exp (t*Real.log (1/c)+(1-t)*Real.log (1/b))*Real.exp ((1-t)^2/4) =
      Real.exp ((1-t)^2/4-t*Real.log (c/b))/b := by
  calc
    _ = Real.exp (t*Real.log (1/c)+(1-t)*Real.log (1/b)+(1-t)^2/4) := (Real.exp_add _ _).symm
    _ = Real.exp ((1-t)^2/4-t*Real.log (c/b)-Real.log b) := by
      congr 1
      rw [Real.log_div hc.ne' hb.ne',one_div,one_div,Real.log_inv,Real.log_inv]
      ring
    _ = _ := by rw [Real.exp_sub,Real.exp_log hb]


lemma exponential_fiber_bound {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (n : ℕ)
    (ih : ∀ B : Set (Fin n → α), 0 < productMass p n B →
      productMean p n (fun x => Real.exp (convexDistanceSq B x/4)) ≤ 1/productMass p n B)
    (A : Set (Fin (n+1) → α)) (hA : 0 < productMass p (n+1) A) (a : α) :
    productMean p n (fun x => Real.exp (convexDistanceSq A (Fin.snoc x a)/4)) ≤
      (2-productMass p n (lastFiber A a)/productMass p n (lastProjection A))/
        productMass p n (lastProjection A) := by
  let b := productMass p n (lastProjection A)
  let c := productMass p n (lastFiber A a)
  have hb : 0 < b := lt_of_lt_of_le hA (productMass_le_projection hp hs A)
  have hc0 : 0 ≤ c := productMass_nonneg hp n _
  have hcb : c ≤ b := productMass_mono hp (lastFiber_subset A a)
  have hbase := ih (lastProjection A) hb
  have hne := productMass_pos_nonempty hA
  by_cases hc : 0 < c
  · obtain ⟨t,ht,ht1,hmix⟩ := mixing_scalar (div_pos hc hb) ((div_le_one hb).mpr hcb)
    have hf := ih (lastFiber A a) hc
    have hfn := productMass_pos_nonempty hc
    have hpoint (x : Fin n → α) : Real.exp (convexDistanceSq A (Fin.snoc x a)/4) ≤
        Real.exp (t*(convexDistanceSq (lastFiber A a) x/4)+(1-t)*(convexDistanceSq (lastProjection A) x/4))*
          Real.exp ((1-t)^2/4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hd := convexDistanceSq_snoc_mix a x hfn ht ht1
      nlinarith
    have havg := finiteMean_exp_mix (productWeight_nonneg hp n) (one_div_pos.mpr hc)
      (one_div_pos.mpr hb) hf hbase ht ht1
    calc
      productMean p n (fun x => Real.exp (convexDistanceSq A (Fin.snoc x a)/4)) ≤
          productMean p n (fun x => Real.exp (t*(convexDistanceSq (lastFiber A a) x/4)+
            (1-t)*(convexDistanceSq (lastProjection A) x/4))*Real.exp ((1-t)^2/4)) :=
        finiteMean_mono (productWeight_nonneg hp n) hpoint
      _ = productMean p n (fun x => Real.exp (t*(convexDistanceSq (lastFiber A a) x/4)+
            (1-t)*(convexDistanceSq (lastProjection A) x/4)))*Real.exp ((1-t)^2/4) :=
        productMean_mul_const _ _ _ _
      _ ≤ Real.exp (t*Real.log (1/c)+(1-t)*Real.log (1/b))*Real.exp ((1-t)^2/4) :=
        mul_le_mul_of_nonneg_right havg (Real.exp_pos _).le
      _ = Real.exp ((1-t)^2/4-t*Real.log (c/b))/b := reciprocal_mix_identity hc hb t
      _ ≤ (2-c/b)/b := div_le_div_of_nonneg_right hmix hb.le
  · have hcz : c=0 := le_antisymm (not_lt.mp hc) hc0
    have hpoint (x : Fin n → α) : Real.exp (convexDistanceSq A (Fin.snoc x a)/4) ≤
        Real.exp (convexDistanceSq (lastProjection A) x/4)*Real.exp (1/4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [convexDistanceSq_snoc_projection hne a x]
    have hm := finiteMean_mono (productWeight_nonneg hp n) hpoint
    change productMean p n _ ≤ productMean p n _ at hm
    rw [productMean_mul_const] at hm
    have he : Real.exp (1/4:ℝ) ≤ 2 := exp_quarter_le.trans (by norm_num)
    change _ ≤ (2-c/b)/b
    rw [hcz,zero_div,sub_zero]
    calc
      _ ≤ (1/b)*Real.exp (1/4) := hm.trans (mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le)
      _ ≤ (1/b)*2 := mul_le_mul_of_nonneg_left he (one_div_pos.mpr hb).le
      _ = 2/b := by ring

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma finiteMean_fiber_expression {α : Type*} [Fintype α] {p : α → ℝ}
    (hs : ∑ a, p a = 1) (c : α → ℝ) (b : ℝ) :
    finiteMean p (fun a => (2-c a/b)/b) = (2-finiteMean p c/b)/b := by
  unfold finiteMean
  calc
    _ = ∑ a, (p a*2/b-(p a*c a)/(b*b)) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (∑ a,p a)*2/b-(∑ a,p a*c a)/(b*b) := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    _ = _ := by rw [hs]; ring


lemma reciprocal_fiber_average {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (2-a/b)/b ≤ 1/a := by
  apply (div_le_div_iff₀ hb ha).mpr
  apply (mul_le_mul_iff_right₀ hb).mp
  have hba : a/b*b=a := div_mul_cancel₀ a hb.ne'
  have he : ((2-a/b)*a)*b = 2*a*b-a^2 := by
    calc
      _ = 2*a*b-a*(a/b*b) := by ring
      _ = _ := by rw [hba]; ring
  rw [mul_comm b ((2-a/b)*a), he]
  nlinarith [sq_nonneg (b-a)]

lemma finite_convex_distance_exponential {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (n : ℕ)
    (A : Set (Fin n → α)) (hA : 0 < productMass p n A) :
    productMean p n (fun x => Real.exp (convexDistanceSq A x/4)) ≤ 1/productMass p n A := by
  induction n with
  | zero =>
      have hne := productMass_pos_nonempty hA
      obtain ⟨x,hx⟩ := hne
      have he : x=Fin.elim0 := Subsingleton.elim _ _
      subst x
      have hm : productMass p 0 A=1 := by
        classical
        unfold productMass
        rw [productMean_zero]
        simp [hx]
      rw [productMean_zero,convexDistanceSq_zero hx,zero_div,Real.exp_zero,hm]
      norm_num
  | succ n ih =>
      have hb : 0 < productMass p n (lastProjection A) :=
        lt_of_lt_of_le hA (productMass_le_projection hp hs A)
      rw [productMean_succ]
      calc
        finiteMean p (fun a => productMean p n (fun x => Real.exp (convexDistanceSq A (Fin.snoc x a)/4))) ≤
            finiteMean p (fun a => (2-productMass p n (lastFiber A a)/productMass p n (lastProjection A))/
              productMass p n (lastProjection A)) :=
          finiteMean_mono hp (fun a => exponential_fiber_bound hp hs n ih A hA a)
        _ = (2-productMass p (n+1) A/productMass p n (lastProjection A))/
              productMass p n (lastProjection A) := by
          rw [finiteMean_fiber_expression hs,← productMass_succ]
        _ ≤ 1/productMass p (n+1) A := reciprocal_fiber_average hA hb

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma finite_convex_distance_tail {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (n : ℕ)
    (A : Set (Fin n → α)) (hA : 0 < productMass p n A) (r : ℝ) :
    productMass p n {x | r ≤ convexDistanceSq A x} ≤
      Real.exp (-r/4) / productMass p n A := by
  classical
  have hmark : productMass p n {x | r ≤ convexDistanceSq A x} * Real.exp (r/4) ≤
      productMean p n (fun x => Real.exp (convexDistanceSq A x/4)) := by
    unfold productMass productMean
    rw [← finiteMean_mul_const]
    apply finiteMean_mono (productWeight_nonneg hp n)
    intro x
    split_ifs with hx
    · simp only [one_mul]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hx (by norm_num))
    · simp only [zero_mul]
      exact (Real.exp_pos _).le
  have h := hmark.trans (finite_convex_distance_exponential hp hs n A hA)
  have heq : (Real.exp (-r/4) / productMass p n A) * Real.exp (r/4) =
      1/productMass p n A := by
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    have he : -r/4+r/4=0 := by ring
    rw [he,Real.exp_zero]
  nlinarith [Real.exp_pos (r/4)]

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma measure_le_of_eventually_mem {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (S : ℕ → Set X) (c : ℝ≥0∞)
    (h : ∀ x ∈ E, ∀ᶠ m in atTop, x ∈ S m) (hb : ∀ m, μ (S m) ≤ c) :
    μ E ≤ c := by
  let T : ℕ → Set X := fun k => ⋂ m ≥ k, S m
  have hT : Monotone T := by
    intro k l hkl x hx
    simp only [T, Set.mem_iInter] at hx ⊢
    exact fun m hlm => hx m (hkl.trans hlm)
  have hsub : E ⊆ ⋃ k, T k := by
    intro x hx
    obtain ⟨k,hk⟩ := eventually_atTop.mp (h x hx)
    exact Set.mem_iUnion.mpr ⟨k,by simpa only [T,Set.mem_iInter] using hk⟩
  calc
    μ E ≤ μ (⋃ k, T k) := measure_mono hsub
    _ = ⨆ k, μ (T k) := hT.measure_iUnion
    _ ≤ c := iSup_le fun k => (measure_mono (by
      intro x hx
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hx k) le_rfl)).trans (hb k)

lemma compact_convex_distance_tail {X : Type*} [MetricSpace X] [MeasurableSpace X]
    {Y : ℕ → Type*} [∀ m, Fintype (Y m)] {n : ℕ}
    (μ : Measure (Fin n → X)) {A : Set (Fin n → X)}
    (hA : IsCompact A) (hne : A.Nonempty)
    (q : (m : ℕ) → X → Y m) (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m)
    (hq : ∀ m x y, q m x=q m y → dist x y ≤ δ m)
    (hlim : Tendsto δ atTop (𝓝 0))
    (p : (m : ℕ) → Y m → ℝ) (hp : ∀ m a, 0 ≤ p m a)
    (hs : ∀ m, ∑ a, p m a = 1)
    (hlaw : ∀ m (B : Set (Fin n → Y m)),
      μ (quantizedPoint (q m) ⁻¹' B) = ENNReal.ofReal (productMass (p m) n B))
    (a : ℝ) (ha : 0 < a) (hμA : ENNReal.ofReal a ≤ μ A) (r : ℝ) :
    μ {x | r ≤ convexDistanceSq A x} ≤ ENNReal.ofReal (Real.exp (-r/4)/a) := by
  apply measure_le_of_eventually_mem μ _
    (fun m => {x | r ≤ convexDistanceSq (quantizedSet (q m) A) (quantizedPoint (q m) x)})
  · intro x hx
    filter_upwards [compact_distance_eventually_equal hA hne q δ hδ hq hlim x] with m hm
    simpa only [Set.mem_ofPred_eq,hm] using hx
  · intro m
    have hmass : a ≤ productMass (p m) n (quantizedSet (q m) A) := by
      apply (ENNReal.ofReal_le_ofReal_iff (productMass_nonneg (hp m) n _)).mp
      apply hμA.trans
      rw [← hlaw]
      exact measure_mono (fun x hx => ⟨x,hx,rfl⟩)
    rw [show {x | r ≤ convexDistanceSq (quantizedSet (q m) A) (quantizedPoint (q m) x)} =
      quantizedPoint (q m) ⁻¹' {z | r ≤ convexDistanceSq (quantizedSet (q m) A) z} from rfl,hlaw]
    apply ENNReal.ofReal_le_ofReal
    exact (finite_convex_distance_tail (hp m) (hs m) n _ (ha.trans_le hmass) r).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le ha hmass)

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace TalagrandConc.Assignment.ACFresh

lemma dyadicSide_tendsto : Tendsto (fun k : ℕ => (2:ℝ)^(-(k:ℤ))) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 < 1)
  simpa only [zpow_neg,zpow_natCast,inv_pow,one_div] using h

lemma cube_compact_convex_tail {n : ℕ} {A : Set (Fin n → unitInterval)}
    (hA : IsCompact A) (hne : A.Nonempty) (a : ℝ) (ha : 0 < a)
    (hμA : ENNReal.ofReal a ≤ cubeLaw n A) (r : ℝ) :
    cubeLaw n {x | r ≤ convexDistanceSq A x} ≤ ENNReal.ofReal (Real.exp (-r/4)/a) := by
  apply compact_convex_distance_tail (cubeLaw n) hA hne intervalIndex
    (fun k => (2:ℝ)^(-(k:ℤ))) (fun k => (dyadicSide_pos k).le)
    (fun _ _ _ h => dist_same_intervalIndex h) dyadicSide_tendsto
    (fun k _ => (2:ℝ)^(-(k:ℤ)))
  · intro m y
    positivity
  · intro m
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    norm_cast
    push_cast
    exact dyadicSide_mul m
  · intro m B
    exact cube_quantized_mass (intervalIndex m) (measurable_intervalIndex m)
      (fun _ => (2:ℝ)^(-(m:ℤ))) (fun _ => (dyadicSide_pos m).le)
      (intervalIndex_atom m) n B
  · exact ha
  · exact hμA

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal BigOperators
namespace TalagrandConc.Assignment.ACFresh

lemma capped_distance_lower {N : ℕ} (hN : 0 < N) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t)
    {A : Set (Fin (N*N) → unitInterval)} (hne : A.Nonempty)
    (x : Fin (N*N) → unitInterval)
    (hgap : ∀ y ∈ A, 8*b*Real.sqrt N*t ≤ cappedObservable N b y-cappedObservable N b x) :
    64*t^2 ≤ convexDistanceSq A x := by
  classical
  obtain ⟨τ,hτ⟩ := cappedObservable_gap hb.le x
  obtain ⟨y,hy,hw⟩ := convexDistance_weight_witness hne x (assignmentWeights τ)
    (assignmentWeights_nonneg τ)
  rw [assignmentWeights_norm] at hw
  have h := (hgap y hy).trans ((hτ y).trans (mul_le_mul_of_nonneg_left hw hb.le))
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hp : 0 < b*Real.sqrt N := mul_pos hb (Real.sqrt_pos.mpr hn)
  have he : (b*Real.sqrt N)*(8*t) ≤ (b*Real.sqrt N)*Real.sqrt (convexDistanceSq A x) := by
    nlinarith [h]
  have hs := (mul_le_mul_iff_right₀ hp).mp he
  have hd := Real.sq_sqrt (convexDistanceSq_nonneg A x)
  nlinarith [sq_nonneg (Real.sqrt (convexDistanceSq A x)-8*t)]

lemma capped_separated_mass {N : ℕ} (hN : 0 < N) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t)
    {A B : Set (Fin (N*N) → unitInterval)} (hA : IsCompact A) (hne : A.Nonempty)
    (a : ℝ) (ha : 0 < a) (hμ : ENNReal.ofReal a ≤ cubeLaw (N*N) A)
    (hgap : ∀ x ∈ B, ∀ y ∈ A, 8*b*Real.sqrt N*t ≤
      cappedObservable N b y-cappedObservable N b x) :
    cubeLaw (N*N) B ≤ ENNReal.ofReal (Real.exp (-16*t^2)/a) := by
  have hsub : B ⊆ {x | 64*t^2 ≤ convexDistanceSq A x} :=
    fun x hx => capped_distance_lower hN hb ht hne x (hgap x hx)
  have he : -(64*t^2)/4 = -16*t^2 := by ring
  have hh := cube_compact_convex_tail hA hne a ha hμ (64*t^2)
  rw [he] at hh
  exact (measure_mono hsub).trans hh

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
namespace TalagrandConc.Assignment.ACFresh

lemma capped_quantile_tails {N : ℕ} (hN : 0 < N) {b t M : ℝ}
    (hb : 0 < b) (ht : 0 ≤ t)
    (hlo : (1/2:ENNReal) ≤ cubeLaw (N*N) {x | cappedObservable N b x ≤ M})
    (hhi : (1/4:ENNReal) ≤ cubeLaw (N*N) {x | M ≤ cappedObservable N b x}) :
    cubeLaw (N*N) {x | M+8*b*Real.sqrt N*t ≤ cappedObservable N b x} ≤
      ENNReal.ofReal (2*Real.exp (-16*t^2)) ∧
    cubeLaw (N*N) {x | cappedObservable N b x ≤ M-8*b*Real.sqrt N*t} ≤
      ENNReal.ofReal (4*Real.exp (-16*t^2)) := by
  constructor
  · let A := {x | M+8*b*Real.sqrt N*t ≤ cappedObservable N b x}
    change cubeLaw (N*N) A ≤ _
    by_cases hz : cubeLaw (N*N) A = 0
    · rw [hz]; exact zero_le
    have hne : A.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty] at hz
      exact hz rfl
    have hcompact : IsCompact A :=
      (isClosed_le continuous_const (continuous_cappedObservable N b)).isCompact
    let a := (cubeLaw (N*N) A).toReal
    have ha : 0 < a := ENNReal.toReal_pos hz (measure_ne_top _ _)
    have hμ : ENNReal.ofReal a ≤ cubeLaw (N*N) A := by
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hbound := capped_separated_mass hN hb ht hcompact hne a ha hμ
      (B := {x | cappedObservable N b x ≤ M}) (by
        intro x hx y hy
        change cappedObservable N b x ≤ M at hx
        change M+8*b*Real.sqrt N*t ≤ cappedObservable N b y at hy
        linarith)
    have hreal : (1/2:ℝ) ≤ Real.exp (-16*t^2)/a := by
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      simpa using hlo.trans hbound
    have har : a ≤ 2*Real.exp (-16*t^2) := by
      have hh := (le_div_iff₀ ha).mp hreal
      linarith
    calc
      _ = ENNReal.ofReal a := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal har
  · let A := {x | M ≤ cappedObservable N b x}
    have hne : A.Nonempty := by
      by_contra h
      have he : A=∅ := Set.not_nonempty_iff_eq_empty.mp h
      change (1/4:ENNReal) ≤ cubeLaw (N*N) A at hhi
      rw [he,measure_empty] at hhi
      norm_num at hhi
    have hcompact : IsCompact A :=
      (isClosed_le continuous_const (continuous_cappedObservable N b)).isCompact
    have hμ : ENNReal.ofReal (1/4:ℝ) ≤ cubeLaw (N*N) A := by simpa using hhi
    have hbound := capped_separated_mass hN hb ht hcompact hne (1/4) (by norm_num) hμ
      (B := {x | cappedObservable N b x ≤ M-8*b*Real.sqrt N*t}) (by
        intro x hx y hy
        change cappedObservable N b x ≤ M-8*b*Real.sqrt N*t at hx
        change M ≤ cappedObservable N b y at hy
        linarith)
    convert hbound using 1
    congr 1
    ring

lemma capped_quantile_absolute_tail {N : ℕ} (hN : 0 < N) {b t M : ℝ}
    (hb : 0 < b) (ht : 0 ≤ t)
    (hlo : (1/2:ENNReal) ≤ cubeLaw (N*N) {x | cappedObservable N b x ≤ M})
    (hhi : (1/4:ENNReal) ≤ cubeLaw (N*N) {x | M ≤ cappedObservable N b x}) :
    cubeLaw (N*N) {x | 8*b*Real.sqrt N*t ≤ |cappedObservable N b x-M|} ≤
      ENNReal.ofReal (6*Real.exp (-16*t^2)) := by
  have h := capped_quantile_tails hN hb ht hlo hhi
  have hsub : {x | 8*b*Real.sqrt N*t ≤ |cappedObservable N b x-M|} ⊆
      {x | M+8*b*Real.sqrt N*t ≤ cappedObservable N b x} ∪
      {x | cappedObservable N b x ≤ M-8*b*Real.sqrt N*t} := by
    intro x hx
    change 8*b*Real.sqrt N*t ≤ |cappedObservable N b x-M| at hx
    rcases le_abs.mp hx with hx | hx
    · apply Or.inl
      change M+8*b*Real.sqrt N*t ≤ cappedObservable N b x
      linarith
    · apply Or.inr
      change cappedObservable N b x ≤ M-8*b*Real.sqrt N*t
      linarith
  calc
    _ ≤ cubeLaw (N*N) ({x | M+8*b*Real.sqrt N*t ≤ cappedObservable N b x} ∪
      {x | cappedObservable N b x ≤ M-8*b*Real.sqrt N*t}) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2*Real.exp (-16*t^2))+ENNReal.ofReal (4*Real.exp (-16*t^2)) :=
      add_le_add h.1 h.2
    _ = ENNReal.ofReal (6*Real.exp (-16*t^2)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end TalagrandConc.Assignment.ACFresh
end

section
namespace TalagrandConc.Assignment.ACFresh

noncomputable def expansionAlpha (N : ℕ) (t : ℝ) : ℝ := 64*max (Real.log N) (t^2)
noncomputable def cycleLength (N : ℕ) (t : ℝ) : ℕ :=
  Nat.ceil (Real.log N/Real.log (expansionAlpha N t))+1
noncomputable def capSize (N : ℕ) (t : ℝ) : ℝ :=
  512*(cycleLength N t:ℝ)*expansionAlpha N t/(N:ℝ)

lemma assignment_log_gt_one (N : ℕ) (hN : 3 ≤ N) : 1 < Real.log (N:ℝ) := by
  have hn : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  apply (Real.lt_log_iff_exp_lt hn0).2
  exact Real.exp_one_lt_three.trans_le hn

lemma assignment_loglog_pos (N : ℕ) (hN : 3 ≤ N) :
    0 < Real.log (Real.log (N:ℝ)) := Real.log_pos (assignment_log_gt_one N hN)

lemma alpha_ge_log (N : ℕ) (t : ℝ) : 64*Real.log (N:ℝ) ≤ expansionAlpha N t :=
  mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
lemma alpha_ge_square (N : ℕ) (t : ℝ) : 64*t^2 ≤ expansionAlpha N t :=
  mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
lemma alpha_ge_sixtyfour (N : ℕ) (hN : 3 ≤ N) (t : ℝ) : 64 ≤ expansionAlpha N t := by
  have h := alpha_ge_log N t
  have hl := assignment_log_gt_one N hN
  linarith
lemma alpha_ge_two (N : ℕ) (hN : 3 ≤ N) (t : ℝ) : 2 ≤ expansionAlpha N t := by
  linarith [alpha_ge_sixtyfour N hN t]
lemma alpha_log_pos (N : ℕ) (hN : 3 ≤ N) (t : ℝ) : 0 < Real.log (expansionAlpha N t) :=
  Real.log_pos (by linarith [alpha_ge_two N hN t])
lemma cycleLength_pos (N : ℕ) (t : ℝ) : 1 ≤ cycleLength N t := by unfold cycleLength; omega
lemma cycleLength_upper (N : ℕ) (hN : 3 ≤ N) (t : ℝ) :
    (cycleLength N t:ℝ) ≤ Real.log N/Real.log (expansionAlpha N t)+2 := by
  have hr : 0 ≤ Real.log (N:ℝ)/Real.log (expansionAlpha N t) :=
    div_nonneg (by linarith [assignment_log_gt_one N hN]) (alpha_log_pos N hN t).le
  have hc := Nat.ceil_lt_add_one hr
  unfold cycleLength
  push_cast
  linarith
lemma alpha_pow_cycleLength (N : ℕ) (hN : 3 ≤ N) (t : ℝ) :
    (N:ℝ) < expansionAlpha N t ^ cycleLength N t := by
  have hn : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ha : 0 < expansionAlpha N t := by linarith [alpha_ge_two N hN t]
  have hl := alpha_log_pos N hN t
  have hc := Nat.le_ceil (Real.log (N:ℝ)/Real.log (expansionAlpha N t))
  have hm : Real.log (N:ℝ)/Real.log (expansionAlpha N t) < (cycleLength N t:ℝ) := by
    unfold cycleLength
    push_cast
    linarith
  apply (Real.log_lt_log_iff hn (pow_pos ha _)).mp
  rw [Real.log_pow]
  exact (div_lt_iff₀ hl).mp hm

end TalagrandConc.Assignment.ACFresh
end

section
namespace TalagrandConc.Assignment.ACFresh

lemma four_exp_shift (a z : ℝ) (h : z+4 ≤ a) :
    4*Real.exp (-a) ≤ Real.exp (-z) := by
  have he : 4 ≤ Real.exp (a-z) := by linarith [Real.add_one_le_exp (a-z)]
  have hp : Real.exp (a-z)*Real.exp (-a) = Real.exp (-z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hp]
  exact mul_le_mul_of_nonneg_right he (Real.exp_pos _).le

lemma alpha_bad_budget (N : ℕ) (hN : 3 ≤ N) (t : ℝ) :
    4*Real.exp (-expansionAlpha N t/2) ≤ Real.exp (-(4*t^2)) ∧
    4*Real.exp (-expansionAlpha N t/2) ≤ 1/4 := by
  have ha := alpha_ge_sixtyfour N hN t
  have ht := alpha_ge_square N t
  constructor
  · have hh := four_exp_shift (expansionAlpha N t/2) (4*t^2) (by nlinarith [sq_nonneg t])
    simpa only [neg_div] using hh
  · have he : 16 ≤ Real.exp (expansionAlpha N t/2) := by
      linarith [Real.add_one_le_exp (expansionAlpha N t/2)]
    have hp : Real.exp (expansionAlpha N t/2)*Real.exp (-expansionAlpha N t/2)=1 := by
      rw [← Real.exp_add]
      have hz : expansionAlpha N t/2 + -expansionAlpha N t/2 = 0 := by ring
      rw [hz,Real.exp_zero]
    have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-expansionAlpha N t/2)).le
    rw [hp] at hm
    linarith

lemma assignment_exp_absorption (t : ℝ) (ht : Real.log 2 ≤ t^2) :
    6*Real.exp (-(16*t^2))+Real.exp (-(4*t^2)) ≤ 2*Real.exp (-(t^2)) := by
  have hex : 2 ≤ Real.exp (t^2) := by
    calc
      (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr ht
  have hprod2 : Real.exp (2*t^2) = Real.exp (t^2)*Real.exp (t^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hge : 4 ≤ Real.exp (3*t^2) := by
    have h2 : 4 ≤ Real.exp (2*t^2) := by rw [hprod2]; nlinarith
    exact h2.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t]))
  have hp : Real.exp (3*t^2)*Real.exp (-(4*t^2)) = Real.exp (-(t^2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : 4*Real.exp (-(4*t^2)) ≤ Real.exp (-(t^2)) := by
    rw [← hp]
    exact mul_le_mul_of_nonneg_right hge (Real.exp_pos _).le
  have h16 : Real.exp (-(16*t^2)) ≤ Real.exp (-(4*t^2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg t]
  nlinarith [Real.exp_pos (-(4*t^2))]

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal
namespace TalagrandConc.Assignment.ACFresh

lemma capSize_pos (N : ℕ) (hN : 3 ≤ N) (t : ℝ) : 0 < capSize N t := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hm : 0 < (cycleLength N t:ℝ) := by unfold cycleLength; positivity
  have ha : 0 < expansionAlpha N t := by linarith [alpha_ge_sixtyfour N hN t]
  unfold capSize
  positivity

lemma native_single_scale {N : ℕ} (hN : 3 ≤ N) {M t : ℝ} (ht : 0 ≤ t)
    (htlarge : Real.log 2 ≤ t^2)
    (hM : TalagrandConc.BinPacking.IsMedian (costLaw N) optCost M)
    {E : Set (Fin (N*N) → unitInterval)}
    (hE : cubeLaw (N*N) E ≤ ENNReal.ofReal (4*Real.exp (-expansionAlpha N t/2)))
    (heq : ∀ x ∉ E, cappedObservable N (capSize N t) x=originalObservable N x) :
    costLaw N {X | 8*capSize N t*Real.sqrt N*t ≤ |optCost X-M|} ≤
      ENNReal.ofReal (2*Real.exp (-(t^2))) := by
  have hbud := alpha_bad_budget N hN t
  have hequarter : cubeLaw (N*N) E ≤ (1/4:ENNReal) := by
    apply hE.trans
    have hh := ENNReal.ofReal_le_ofReal hbud.2
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4),
      ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using hh
  have hq := capped_quantiles hM hequarter heq
  have hcap := capped_quantile_absolute_tail (by omega : 0 < N) (capSize_pos N hN t) ht hq.1 hq.2
  calc
    _ ≤ cubeLaw (N*N) E+cubeLaw (N*N) {x | 8*capSize N t*Real.sqrt N*t ≤
      |cappedObservable N (capSize N t) x-M|} := native_tail_le_capped _ _ _ heq
    _ ≤ ENNReal.ofReal (Real.exp (-(4*t^2)))+ENNReal.ofReal (6*Real.exp (-16*t^2)) :=
      add_le_add (hE.trans (ENNReal.ofReal_le_ofReal hbud.1)) hcap
    _ = ENNReal.ofReal (6*Real.exp (-(16*t^2))+Real.exp (-(4*t^2))) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      simp only [neg_mul,add_comm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (assignment_exp_absorption t htlarge)

end TalagrandConc.Assignment.ACFresh
end

section
namespace TalagrandConc.Assignment.ACFresh

lemma cycleLength_three_ratio (N : ℕ) (hN : 3 ≤ N) (t d : ℝ)
    (hd : 0 < d) (hda : d ≤ Real.log (expansionAlpha N t))
    (hdn : d ≤ Real.log (N:ℝ)) :
    (cycleLength N t:ℝ) ≤ 3*Real.log (N:ℝ)/d := by
  have ha : 0 ≤ Real.log (N:ℝ) := by linarith [assignment_log_gt_one N hN]
  have hratio := div_le_div_of_nonneg_left ha hd hda
  have hone : 1 ≤ Real.log (N:ℝ)/d := (le_div_iff₀ hd).2 (by simpa using hdn)
  have hm := cycleLength_upper N hN t
  calc
    _ ≤ Real.log (N:ℝ)/d+2 := by linarith
    _ ≤ 3*Real.log (N:ℝ)/d := by
      rw [mul_div_assoc]
      nlinarith

lemma cap_gap_eq (N : ℕ) (hN : 0 < N) (t : ℝ) :
    8*capSize N t*Real.sqrt N*t =
      4096*(cycleLength N t:ℝ)*expansionAlpha N t*t/Real.sqrt N := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.2 hn
  have he := Real.sq_sqrt hn.le
  unfold capSize
  apply (eq_div_iff hs.ne').2
  field_simp
  rw [he]
  ring

lemma low_scale_budget (N : ℕ) (hN : 3 ≤ N) (t : ℝ) (ht : 0 ≤ t)
    (hlow : t^2 ≤ Real.log (N:ℝ)) :
    8*capSize N t*Real.sqrt N*t ≤
      786432*t*Real.log (N:ℝ)^2/(Real.sqrt N*Real.log (Real.log (N:ℝ))) := by
  have ha : 0 < Real.log (N:ℝ) := by linarith [assignment_log_gt_one N hN]
  have hd := assignment_loglog_pos N hN
  have hda : Real.log (Real.log (N:ℝ)) ≤ Real.log (expansionAlpha N t) := by
    apply Real.log_le_log ha
    nlinarith [alpha_ge_log N t]
  have hdn : Real.log (Real.log (N:ℝ)) ≤ Real.log (N:ℝ) := by
    linarith [Real.log_le_sub_one_of_pos ha]
  have hm := cycleLength_three_ratio N hN t _ hd hda hdn
  have halpha : expansionAlpha N t = 64*Real.log (N:ℝ) := by
    unfold expansionAlpha
    rw [max_eq_left hlow]
  have hn : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [cap_gap_eq N (by omega) t,halpha]
  calc
    _ = (262144*t*Real.log (N:ℝ)/Real.sqrt N)*(cycleLength N t:ℝ) := by ring
    _ ≤ (262144*t*Real.log (N:ℝ)/Real.sqrt N)*(3*Real.log (N:ℝ)/Real.log (Real.log (N:ℝ))) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

lemma high_scale_budget (N : ℕ) (hN : 3 ≤ N) (t : ℝ) (ht : 0 ≤ t)
    (hhigh : Real.log (N:ℝ) ≤ t^2) (hsmall : t^2 ≤ (N:ℝ)) :
    8*capSize N t*Real.sqrt N*t ≤
      786432*t^3*Real.log (N:ℝ)/(Real.sqrt N*Real.log (t^2)) := by
  have ha : 1 < t^2 := (assignment_log_gt_one N hN).trans_le hhigh
  have hd : 0 < Real.log (t^2) := Real.log_pos ha
  have hda : Real.log (t^2) ≤ Real.log (expansionAlpha N t) := by
    apply Real.log_le_log (by linarith)
    nlinarith [alpha_ge_square N t]
  have hdn : Real.log (t^2) ≤ Real.log (N:ℝ) := Real.log_le_log (by linarith) hsmall
  have hm := cycleLength_three_ratio N hN t _ hd hda hdn
  have halpha : expansionAlpha N t = 64*t^2 := by
    unfold expansionAlpha
    rw [max_eq_right hhigh]
  have hn : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [cap_gap_eq N (by omega) t,halpha]
  calc
    _ = (262144*t^3/Real.sqrt N)*(cycleLength N t:ℝ) := by ring
    _ ≤ (262144*t^3/Real.sqrt N)*(3*Real.log (N:ℝ)/Real.log (t^2)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end TalagrandConc.Assignment.ACFresh
end

section
namespace TalagrandConc.Assignment.ACFresh

lemma high_scale_base_ge_size (N : ℕ) (hN : 3 ≤ N) (t : ℝ)
    (ht : 0 ≤ t) (hlarge : (N:ℝ) ≤ t^2) :
    (N:ℝ) ≤ t^3*Real.log (N:ℝ)/(Real.sqrt N*Real.log (t^2)) := by
  have hn : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn3 : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.2 hn
  have hs2 := Real.sq_sqrt hn.le
  have hst : Real.sqrt (N:ℝ) ≤ t := by nlinarith [Real.sqrt_nonneg (N:ℝ)]
  let u := t/Real.sqrt (N:ℝ)
  have hu : 1 ≤ u := (le_div_iff₀ hs).2 (by simpa using hst)
  have hu0 : 0 < u := by linarith
  have heq : t=Real.sqrt (N:ℝ)*u := by dsimp [u]; field_simp
  have hrel : t^2=(N:ℝ)*u^2 := by rw [heq]; nlinarith [sq_nonneg u]
  have ha : 1 < Real.log (N:ℝ) := assignment_log_gt_one N hN
  have hb : 0 < Real.log (t^2) := Real.log_pos (by nlinarith)
  have hlog : Real.log (t^2)=Real.log (N:ℝ)+2*Real.log u := by
    rw [hrel, Real.log_mul hn.ne' (pow_pos hu0 2).ne',Real.log_pow]
    norm_num
  have hlu := Real.log_le_sub_one_of_pos hu0
  have hu3 : 2*(u-1) ≤ u^3-1 := by
    have hh := mul_nonneg (show 0 ≤ u-1 by linarith)
      (show 0 ≤ u^2+u-1 by nlinarith)
    nlinarith
  have hcore : Real.log (N:ℝ)+2*Real.log u ≤ u^3*Real.log (N:ℝ) := by
    have hh := mul_nonneg (show 0 ≤ Real.log (N:ℝ)-1 by linarith)
      (show 0 ≤ u^3-1 by nlinarith)
    nlinarith
  apply (le_div_iff₀ (mul_pos hs hb)).2
  have hm := mul_le_mul_of_nonneg_left hcore
    (show 0 ≤ (N:ℝ)*Real.sqrt (N:ℝ) by positivity)
  rw [← hlog] at hm
  have he : (N:ℝ)*Real.sqrt (N:ℝ)*(u^3*Real.log (N:ℝ)) = t^3*Real.log (N:ℝ) := by
    calc
      _ = (Real.sqrt (N:ℝ))^2*Real.sqrt (N:ℝ)*(u^3*Real.log (N:ℝ)) := by rw [hs2]
      _ = _ := by rw [heq]; ring
  rw [he] at hm
  nlinarith

lemma high_scale_strict_range (N : ℕ) (hN : 3 ≤ N) (t K : ℝ)
    (ht : 0 ≤ t) (hlarge : (N:ℝ) ≤ t^2) (hK : 1 < K) :
    (N:ℝ) < K*t^3*Real.log (N:ℝ)/(Real.sqrt N*Real.log (t^2)) := by
  have hb := high_scale_base_ge_size N hN t ht hlarge
  have hn : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : 0 < t^3*Real.log (N:ℝ)/(Real.sqrt N*Real.log (t^2)) := hn.trans_le hb
  have hh := mul_pos (show 0 < K-1 by linarith) hp
  calc
    _ < K*(t^3*Real.log (N:ℝ)/(Real.sqrt N*Real.log (t^2))) := by nlinarith
    _ = _ := by ring

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal
namespace TalagrandConc.Assignment.ACFresh

lemma trivial_small_tail (N : ℕ) (B : Set (Fin N × Fin N → ℝ)) (t : ℝ)
    (ht : t^2 ≤ Real.log 2) : costLaw N B ≤ ENNReal.ofReal (2*Real.exp (-(t^2))) := by
  have he : (1:ℝ) ≤ 2*Real.exp (-(t^2)) := by
    have hh := Real.exp_le_exp.mpr ht
    rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
    have hp : Real.exp (t^2)*Real.exp (-(t^2))=1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(t^2))).le]
  calc
    _ ≤ costLaw N Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ
    _ ≤ _ := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he

lemma native_concentration_of_scales
    (hscale : ∀ N : ℕ, 3 ≤ N → ∀ M t : ℝ, 0 ≤ t → Real.log 2 ≤ t^2 →
      TalagrandConc.BinPacking.IsMedian (costLaw N) optCost M →
      costLaw N {X | 8*capSize N t*Real.sqrt N*t ≤ |optCost X-M|} ≤
        ENNReal.ofReal (2*Real.exp (-(t^2)))) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 3 ≤ N → ∀ M : ℝ,
      TalagrandConc.BinPacking.IsMedian (costLaw N) optCost M → ∀ t : ℝ, 0 ≤ t →
        (t ≤ Real.sqrt (Real.log N) →
          costLaw N {X | K*t*Real.log N^2/(Real.sqrt N*Real.log (Real.log N)) ≤ |optCost X-M|} ≤
            ENNReal.ofReal (2*Real.exp (-t^2))) ∧
        (Real.sqrt (Real.log N) ≤ t →
          costLaw N {X | K*t^3*Real.log N/(Real.sqrt N*Real.log (t^2)) ≤ |optCost X-M|} ≤
            ENNReal.ofReal (2*Real.exp (-t^2))) := by
  refine ⟨1048576,by norm_num,?_⟩
  intro N hN M hM t ht
  have hn : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hl : 0 < Real.log (N:ℝ) := by linarith [assignment_log_gt_one N hN]
  have hd := assignment_loglog_pos N hN
  by_cases hs : t^2 ≤ Real.log 2
  · constructor <;> intro _ <;> exact trivial_small_tail N _ t hs
  have hscale' := hscale N hN M t ht (le_of_not_ge hs) hM
  have hr := Real.sq_sqrt hl.le
  constructor
  · intro hlow
    have hlow2 : t^2 ≤ Real.log (N:ℝ) := by nlinarith [Real.sqrt_nonneg (Real.log (N:ℝ))]
    have hb := low_scale_budget N hN t ht hlow2
    have hb' : 786432*t*Real.log (N:ℝ)^2/(Real.sqrt N*Real.log (Real.log (N:ℝ))) ≤
        1048576*t*Real.log (N:ℝ)^2/(Real.sqrt N*Real.log (Real.log (N:ℝ))) := by gcongr; norm_num
    exact (measure_mono (fun X hx => (hb.trans hb').trans hx)).trans hscale'
  · intro hhigh
    have hhigh2 : Real.log (N:ℝ) ≤ t^2 := by nlinarith [Real.sqrt_nonneg (Real.log (N:ℝ))]
    by_cases hlarge : (N:ℝ) ≤ t^2
    · rw [native_tail_zero_of_range hM (high_scale_strict_range N hN t 1048576 ht hlarge (by norm_num : (1:ℝ)<1048576))]
      exact zero_le
    · have hb := high_scale_budget N hN t ht hhigh2 (le_of_not_ge hlarge)
      have hdt : 0 < Real.log (t^2) := Real.log_pos ((assignment_log_gt_one N hN).trans_le hhigh2)
      have hb' : 786432*t^3*Real.log (N:ℝ)/(Real.sqrt N*Real.log (t^2)) ≤
          1048576*t^3*Real.log (N:ℝ)/(Real.sqrt N*Real.log (t^2)) := by gcongr; norm_num
      exact (measure_mono (fun X hx => (hb.trans hb').trans hx)).trans hscale'

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

theorem productMean_exp_sum {α : Type*} [Fintype α]
    (p f : α → ℝ) (N : ℕ) :
    productMean p N (fun x => Real.exp (∑ i, f (x i)))=
      (∑ a, p a*Real.exp (f a))^N := by
  unfold productMean finiteMean productWeight
  simp only [Real.exp_sum,← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun a => p a*Real.exp (f a)) N).symm

theorem productMass_le_exp_moment {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (N : ℕ)
    (f : (Fin N → α) → ℝ) (b : ℝ) :
    productMass p N {x | b ≤ f x} ≤
      Real.exp (-b)*productMean p N (fun x => Real.exp (f x)) := by
  classical
  have h := finiteMean_mono (productWeight_nonneg hp N)
    (f := fun x => if b ≤ f x then (1:ℝ) else 0)
    (g := fun x => Real.exp (-b)*Real.exp (f x)) (by
      intro x
      by_cases hx : b ≤ f x
      · simp only [hx,ite_true]
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      · simp only [hx,ite_false]
        positivity)
  change productMass p N {x | b ≤ f x} ≤ _ at h
  have he : finiteMean (productWeight p N) (fun x => Real.exp (-b)*Real.exp (f x))=
      Real.exp (-b)*productMean p N (fun x => Real.exp (f x)) := by
    unfold productMean
    unfold finiteMean
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  exact h.trans_eq he

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

theorem productMass_finite_union {α I : Type*} [Fintype α] [DecidableEq I]
    (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (N : ℕ) (S : Finset I)
    (A : I → Set (Fin N → α)) :
    productMass p N {x | ∃ i ∈ S, x ∈ A i} ≤ ∑ i ∈ S, productMass p N (A i) := by
  classical
  unfold productMass productMean finiteMean
  have hp := productWeight_nonneg hp0 N
  calc
    _ ≤ ∑ x, productWeight p N x * (∑ i ∈ S, if x ∈ A i then (1:ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (hp x)
      by_cases h : ∃ i ∈ S, x ∈ A i
      · simp only [Set.mem_ofPred_eq,h,ite_true]
        obtain ⟨i,hi,hxi⟩ := h
        have hh := Finset.single_le_sum (f := fun j => if x ∈ A j then (1:ℝ) else 0)
          (fun j hj => by split_ifs <;> norm_num) hi
        simpa only [hxi,ite_true] using hh
      · simp only [Set.mem_ofPred_eq,h,ite_false]
        exact Finset.sum_nonneg (fun j hj => by split_ifs <;> norm_num)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

/-- A matrix is grouped by columns; within each column the coordinates are rows. -/
def columnsEquiv (N : ℕ) : (Fin N → Fin N → Bool) ≃ (Fin (N*N) → Bool) where
  toFun c i := c (edgeEquiv N i).2 (edgeEquiv N i).1
  invFun x j i := x ((edgeEquiv N).symm (i,j))
  left_inv c := by funext j i; simp
  right_inv x := by
    funext i
    exact congrArg x ((edgeEquiv N).symm_apply_apply i)

lemma productWeight_columns (w : Bool → ℝ) (N : ℕ) (c : Fin N → Fin N → Bool) :
    productWeight (productWeight w N) N c = productWeight w (N*N) (columnsEquiv N c) := by
  unfold productWeight
  change (∏ j, ∏ i, w (c j i)) = ∏ a, w (c (edgeEquiv N a).2 (edgeEquiv N a).1)
  rw [(edgeEquiv N).prod_comp (fun a => w (c a.2 a.1)), Fintype.prod_prod_type]
  exact Finset.prod_comm

lemma productMass_columns (w : Bool → ℝ) (N : ℕ) (A : Set (Fin (N*N) → Bool)) :
    productMass w (N*N) A =
      productMass (productWeight w N) N (columnsEquiv N ⁻¹' A) := by
  classical
  unfold productMass productMean finiteMean
  rw [← (columnsEquiv N).sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  rw [← productWeight_columns]
  rfl

/-- Restrict a column to the chosen row set; indicator of at least one present edge. -/
noncomputable def columnHit {N : ℕ} (S : Finset (Fin N)) (c : Fin N → Bool) : Bool :=
  if ∃ i ∈ S, c i=true then true else false

lemma columnHit_false_iff {N : ℕ} (S : Finset (Fin N)) (c : Fin N → Bool) :
    columnHit S c=false ↔ ∀ i ∈ S, c i=false := by
  classical
  simp [columnHit]

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment.ACFresh

/-- A positive directed closed walk, represented with natural-number indices. -/
def ClosedWalk {V : Type*} (R : V → V → Prop) (i : V) (n : ℕ) (c : ℕ → V) : Prop :=
  0 < n ∧ c 0 = i ∧ c n = i ∧ ∀ k, k < n → R (c k) (c (k+1))

lemma closedWalk_shorten {V : Type*} {R : V → V → Prop} {i : V}
    {n : ℕ} {c : ℕ → V} (h : ClosedWalk R i n c)
    {a b : ℕ} (hab : a < b) (hbn : b < n) (he : c a = c b) :
    ∃ d : ℕ → V, ClosedWalk R i (n-(b-a)) d := by
  let d : ℕ → V := fun k => if k < a then c k else c (k+(b-a))
  have hdn : n-(b-a)+(b-a)=n := by omega
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · omega
  · dsimp [d]
    split_ifs with ha
    · exact h.2.1
    · have ha0 : a=0 := by omega
      subst a
      simpa using he.symm.trans h.2.1
  · dsimp [d]
    rw [if_neg (by omega), hdn]
    exact h.2.2.1
  · intro k hk
    dsimp [d]
    by_cases hka : k+1<a
    · rw [if_pos (by omega), if_pos hka]
      exact h.2.2.2 k (by omega)
    · by_cases hkl : k<a
      · have hkaeq : k+1=a := by omega
        rw [if_pos hkl, if_neg hka]
        have heq : k+1+(b-a)=b := by omega
        rw [heq, ← he, ← hkaeq]
        exact h.2.2.2 k (by omega)
      · rw [if_neg hkl, if_neg hka]
        convert h.2.2.2 (k+(b-a)) (by omega) using 1
        congr 1
        omega

lemma closedWalk_exists_simple {V : Type*} {R : V → V → Prop} {i : V}
    {L : ℕ} {c : ℕ → V} (h : ClosedWalk R i L c) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ L ∧ ∃ d : ℕ → V,
      ClosedWalk R i n d ∧ ∀ a b, a<n → b<n → d a=d b → a=b := by
  classical
  have hex : ∃ n : ℕ, ∃ d : ℕ → V, ClosedWalk R i n d := ⟨L,c,h⟩
  let n := Nat.find hex
  obtain ⟨d,hd⟩ := Nat.find_spec hex
  refine ⟨n, hd.1, Nat.find_min' hex ⟨c,h⟩, d, hd, ?_⟩
  intro a b ha hb he
  by_contra hn
  have hab : a<b ∨ b<a := lt_or_gt_of_ne hn
  rcases hab with hab | hba
  · obtain ⟨e,he'⟩ := closedWalk_shorten hd hab hb he
    have hmin := Nat.find_min' hex (show ∃ e, ClosedWalk R i (n-(b-a)) e from ⟨e,he'⟩)
    omega
  · obtain ⟨e,he'⟩ := closedWalk_shorten hd hba ha he.symm
    have hmin := Nat.find_min' hex (show ∃ e, ClosedWalk R i (n-(a-b)) e from ⟨e,he'⟩)
    omega

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment.ACFresh

def relNbhd {V : Type*} (R : V → V → Prop) (S : Set V) : Set V :=
  {y | ∃ x  ∈  S, R x y}

def strongGrowth (N : ℕ) (α : ℝ) (R : Fin N → Fin N → Prop) : Prop :=
  ∀ S : Set (Fin N), min (α * S.ncard) (3*(N:ℝ)/4)  ≤  ((relNbhd R S).ncard : ℝ)

def reach {V : Type*} (R : V → V → Prop) (i : V) : ℕ → Set V
  | 0 => {i}
  | k+1 => relNbhd R (reach R i k)

lemma grow_min {α a C r : ℝ} (hα : 1  ≤  α) (hC : 0  ≤  C)
    (h : min a C  ≤  r) : min (α*a) C  ≤  min (α*r) C := by
  by_cases ha : a  ≤  C
  · rw [min_eq_left ha] at h
    exact min_le_min_right C (mul_le_mul_of_nonneg_left h (by linarith))
  · rw [min_eq_right (le_of_not_ge ha)] at h
    have hCr : C  ≤  α*r := by nlinarith
    rw [min_eq_right hCr]
    exact min_le_right _ _

lemma reach_card {N : ℕ} {α : ℝ} {R : Fin N → Fin N → Prop}
    (hα : 1  ≤  α) (hR : strongGrowth N α R) (i : Fin N) (k : ℕ) :
    min (α^k) (3*(N:ℝ)/4)  ≤  ((reach R i k).ncard : ℝ) := by
  induction k with
  | zero => simp [reach]
  | succ k ih =>
    calc
      min (α^(k+1)) (3*(N:ℝ)/4) = min (α*α^k) (3*(N:ℝ)/4) := by rw [pow_succ, mul_comm]
      _  ≤  min (α*((reach R i k).ncard : ℝ)) (3*(N:ℝ)/4) := grow_min hα (by positivity) ih
      _  ≤  ((reach R i (k+1)).ncard : ℝ) := hR _

lemma reach_has_path {V : Type*} {R : V → V → Prop} {i j : V} {k : ℕ}
    (h : j  ∈  reach R i k) :
    ∃ c : ℕ → V, c 0=i ∧ c k=j ∧ ∀ a, a < k → R (c a) (c (a+1)) := by
  induction k generalizing j with
  | zero =>
    have hj : j=i := h
    subst j
    exact ⟨fun _ => i, rfl, rfl, by intro a ha; omega⟩
  | succ k ih =>
    obtain ⟨v,hv,hvj⟩ := h
    obtain ⟨c,hc0,hck,hc⟩ := ih hv
    let d : ℕ → V := fun a => if a ≤ k then c a else j
    refine ⟨d, ?_, ?_, ?_⟩
    · simpa [d] using hc0
    · simp [d]
    · intro a ha
      dsimp [d]
      by_cases hak : a < k
      · rw [if_pos (by omega), if_pos (by omega)]
        exact hc a hak
      · have he : a=k := by omega
        subst a
        simpa [hck] using hvj

lemma paths_closedWalk {V : Type*} {R : V → V → Prop} {i j : V} {m : ℕ}
    (hm : 0  <  m) {c d : ℕ → V} (hc0 : c 0=i) (hcm : c m=j)
    (hc : ∀ a, a < m → R (c a) (c (a+1)))
    (hd0 : d 0=i) (hdm : d m=j) (hd : ∀ a, a < m → R (d (a+1)) (d a)) :
    ∃ e : ℕ → V, ClosedWalk R i (2*m) e := by
  let e : ℕ → V := fun a => if a ≤ m then c a else d (2*m-a)
  refine ⟨e, by omega, ?_, ?_, ?_⟩
  · simpa [e] using hc0
  · simpa [e, show ¬2*m ≤ m by omega] using hd0
  · intro a ha
    dsimp [e]
    by_cases ham : a < m
    · rw [if_pos (by omega), if_pos (by omega)]
      exact hc a ham
    · have hnext : ¬a+1 ≤ m := by omega
      rw [if_neg hnext]
      by_cases heq : a=m
      · subst a
        rw [if_pos le_rfl, hcm, ← hdm]
        have hindex : 2*m-(m+1)=m-1 := by omega
        rw [hindex]
        convert hd (m-1) (by omega) using 1
        congr 1
        omega
      · rw [if_neg (by omega)]
        convert hd (2*m-(a+1)) (by omega) using 1
        congr 1
        omega

lemma strongGrowth_closedWalk {N : ℕ} (hN : 0  <  N) {α : ℝ}
    (hα : 1 ≤ α) {R : Fin N → Fin N → Prop}
    (hR : strongGrowth N α R) (hRr : strongGrowth N α (fun x y => R y x))
    {m : ℕ} (hm : 0  <  m) (hpow : (N:ℝ) < α^m) (i : Fin N) :
    ∃ c : ℕ → Fin N, ClosedWalk R i (2*m) c := by
  have hcap : 3*(N:ℝ)/4  ≤  α^m := by
    have : (0:ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hf := reach_card hα hR i m
  have hb := reach_card hα hRr i m
  rw [min_eq_right hcap] at hf hb
  have hne : ((reach R i m) ∩ reach (fun x y => R y x) i m).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    have hu := Set.ncard_le_card ((reach R i m) ∪ reach (fun x y => R y x) i m)
    have hadd := Set.ncard_union_add_ncard_inter (reach R i m) (reach (fun x y => R y x) i m)
    rw [he, Set.ncard_empty, add_zero] at hadd
    have hsum : (reach R i m).ncard + (reach (fun x y => R y x) i m).ncard  ≤  N := by
      simpa [hadd] using hu
    have hsum' : ((reach R i m).ncard:ℝ) + (reach (fun x y => R y x) i m).ncard  ≤  N := by exact_mod_cast hsum
    have hN' : (0:ℝ) < N := by exact_mod_cast hN
    linarith
  obtain ⟨j,hj,hjr⟩ := hne
  obtain ⟨c,hc0,hcm,hc⟩ := reach_has_path hj
  obtain ⟨d,hd0,hdm,hd⟩ := reach_has_path hjr
  exact paths_closedWalk hm hc0 hcm hc hd0 hdm hd

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment.ACFresh

/-- The finite probabilistic event only requires small subsets. -/
def smallGrowth (N : ℕ) (α : ℝ) (R : Fin N → Fin N → Prop) : Prop :=
  ∀ S : Set (Fin N), (S.ncard : ℝ)  ≤  (N:ℝ)/2 →
    min (α*S.ncard) (3*(N:ℝ)/4)  ≤  ((relNbhd R S).ncard : ℝ)

lemma relNbhd_mono {V : Type*} (R : V → V → Prop) {S T : Set V} (h : S ⊆ T) :
    relNbhd R S  ⊆  relNbhd R T := by
  rintro y ⟨x,hx,hxy⟩
  exact ⟨x,h hx,hxy⟩

lemma smallGrowth_strongGrowth {N : ℕ} (hN : 3 ≤ N) {α : ℝ} (hα : 3 ≤ α)
    {R : Fin N → Fin N → Prop} (hR : smallGrowth N α R) : strongGrowth N α R := by
  intro S
  by_cases hS : (S.ncard:ℝ) ≤ (N:ℝ)/2
  · exact hR S hS
  · have hS' : N/2  ≤  S.ncard := by
      have hf : ((N/2:ℕ):ℝ)  ≤  (N:ℝ)/2 := by
        have hn : 2*(N/2) ≤ N := by omega
        have hn' : (2:ℝ)*(N/2:ℕ) ≤ N := by exact_mod_cast hn
        linarith
      exact_mod_cast hf.trans (le_of_not_ge hS)
    obtain ⟨T,hTS,hT⟩ := Set.exists_subset_card_eq hS'
    have hhalf' : ((N/2:ℕ):ℝ) ≤ (N:ℝ)/2 := by
      have hh : (2:ℝ)*(N/2:ℕ) ≤ N := by exact_mod_cast (show 2*(N/2) ≤ N by omega)
      linarith
    have hthird : (N:ℝ) ≤ 3*(N/2:ℕ) := by exact_mod_cast (show N ≤ 3*(N/2) by omega)
    have hcap : 3*(N:ℝ)/4  ≤  α*(N/2:ℕ) := by
      have hz : (0:ℝ) ≤ (N/2:ℕ) := Nat.cast_nonneg _
      nlinarith
    have hg := hR T (by simpa [hT] using hhalf')
    rw [hT,min_eq_right hcap] at hg
    exact (min_le_right _ _).trans (hg.trans (by exact_mod_cast Set.ncard_le_ncard (relNbhd_mono R hTS)))

lemma strongGrowth_target_perm {N : ℕ} {α : ℝ} {R : Fin N → Fin N → Prop}
    (hR : strongGrowth N α R) (τ : Equiv.Perm (Fin N)) :
    strongGrowth N α (fun x y => R x (τ y)) := by
  intro S
  have he : relNbhd (fun x y => R x (τ y)) S = τ ⁻¹' relNbhd R S := rfl
  rw [he, Set.ncard_preimage_of_injective_subset_range τ.injective (by simp)]
  exact hR S

lemma strongGrowth_source_perm {N : ℕ} {α : ℝ} {R : Fin N → Fin N → Prop}
    (hR : strongGrowth N α R) (τ : Equiv.Perm (Fin N)) :
    strongGrowth N α (fun x y => R (τ x) y) := by
  intro S
  have he : relNbhd (fun x y => R (τ x) y) S = relNbhd R (τ '' S) := by
    ext y
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨τ x,⟨x,hx,rfl⟩,hxy⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,hxy⟩
      exact ⟨x,hx,hxy⟩
  rw [he]
  simpa only [Set.ncard_image_of_injective S τ.injective] using hR (τ '' S)

lemma smallGrowth_simple_alternating_cycle {N : ℕ} (hN : 3 ≤ N) {α : ℝ}
    (hα : 3 ≤ α) {D : Set (Fin N × Fin N)}
    (hD : smallGrowth N α (fun x y => (x,y) ∈ D))
    (hDr : smallGrowth N α (fun x y => (y,x) ∈ D))
    {m : ℕ} (hm : 0  <  m) (hpow : (N:ℝ) < α^m)
    (τ : Equiv.Perm (Fin N)) (i : Fin N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2*m ∧ ∃ c : ℕ → Fin N,
      ClosedWalk (fun x y => (x,τ y) ∈ D) i n c ∧
      ∀ a b, a < n → b < n → c a=c b → a=b := by
  have hforward := strongGrowth_target_perm (smallGrowth_strongGrowth hN hα hD) τ
  have hbackward := strongGrowth_source_perm (smallGrowth_strongGrowth hN hα hDr) τ
  obtain ⟨c,hc⟩ := strongGrowth_closedWalk (by omega : 0  <  N) (by linarith : 1 ≤ α)
    hforward hbackward hm hpow i
  exact closedWalk_exists_simple hc

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma bernoulliWeight_sum (p : ℝ) : ∑ b : Bool, bernoulliWeight p b = 1 := by
  simp [bernoulliWeight]

lemma productMass_rectangle {A : Type*} [Fintype A] (w : A → ℝ) (n : ℕ)
    (P : Fin n → A → Prop) [∀ i a, Decidable (P i a)] :
    productMass w n {x | ∀ i, P i (x i)} = ∏ i, ∑ a, w a * if P i a then 1 else 0 := by
  classical
  unfold productMass productMean finiteMean productWeight
  rw [Fintype.prod_sum (fun (i : Fin n) (a : A) => w a * if P i a then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib, Fintype.prod_boole]
  simp only [Set.mem_ofPred_eq]
  split_ifs <;> rfl

lemma columnHit_false_mass {N : ℕ} (p : ℝ) (S : Finset (Fin N)) :
    productMass (bernoulliWeight p) N {c | columnHit S c=false}=(1-p)^S.card := by
  classical
  have he : {c : Fin N → Bool | columnHit S c=false}={c | ∀ i, i ∈ S → c i=false} := by
    ext c
    exact columnHit_false_iff S c
  rw [he,productMass_rectangle (bernoulliWeight p) N (fun i a => i ∈ S → a=false)]
  have hf : ∀ i : Fin N, (∑ a : Bool, bernoulliWeight p a * if i ∈ S → a=false then 1 else 0)=
      if i ∈ S then 1-p else 1 := by
    intro i
    by_cases hi : i ∈ S <;> simp [hi,bernoulliWeight]
  simp_rw [hf]
  simp

lemma columnHit_exp_moment {N : ℕ} (p : ℝ) (S : Finset (Fin N)) :
    (∑ c : Fin N → Bool, productWeight (bernoulliWeight p) N c *
      Real.exp (-(if columnHit S c=true then (1:ℝ) else 0))) =
      1-(1-(1-p)^S.card)*(1-Real.exp (-1)) := by
  classical
  have hnorm : ∑ c : Fin N → Bool, productWeight (bernoulliWeight p) N c=1 :=
    productWeight_sum (bernoulliWeight_sum p) N
  have hmoment : ∀ c : Fin N → Bool,
      Real.exp (-(if columnHit S c=true then (1:ℝ) else 0)) =
        Real.exp (-1)+(1-Real.exp (-1))*(if columnHit S c=false then 1 else 0) := by
    intro c
    cases columnHit S c <;> simp
  simp_rw [hmoment, mul_add, mul_left_comm _ (1-Real.exp (-1))]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hnorm, one_mul, ← Finset.mul_sum]
  have hz := columnHit_false_mass p S
  simp only [productMass,productMean,finiteMean,Set.mem_ofPred_eq] at hz
  calc
    _ = Real.exp (-1)+(1-Real.exp (-1))*(1-p)^S.card := by
      congr 1
      congr 1
      convert hz using 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : columnHit S x=false <;> simp [hx]
    _ = _ := by ring

lemma columnHit_moment_bound {N : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (S : Finset (Fin N)) :
    (∑ c : Fin N → Bool, productWeight (bernoulliWeight p) N c *
      Real.exp (-(if columnHit S c=true then (1:ℝ) else 0)))  ≤ 
      Real.exp (-(1-(1-p)^S.card)/2) := by
  rw [columnHit_exp_moment]
  have hz : (1-p)^S.card ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have he : Real.exp (-1) ≤ (1:ℝ)/2 := by
    rw [Real.exp_neg]
    have h := Real.add_one_le_exp (1:ℝ)
    exact (inv_le_comm₀ (Real.exp_pos 1) (by norm_num)).mpr (by linarith)
  have hexp := Real.add_one_le_exp (-(1-(1-p)^S.card)/2)
  nlinarith

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma columnMiss_exp_moment {N : ℕ} (p lam : ℝ) (S : Finset (Fin N)) :
    (∑ c : Fin N → Bool, productWeight (bernoulliWeight p) N c *
      Real.exp (lam*(if columnHit S c=false then (1:ℝ) else 0))) =
      1+(Real.exp lam-1)*(1-p)^S.card := by
  classical
  have hnorm : ∑ c : Fin N → Bool, productWeight (bernoulliWeight p) N c=1 :=
    productWeight_sum (bernoulliWeight_sum p) N
  have hmoment : ∀ c : Fin N → Bool,
      Real.exp (lam*(if columnHit S c=false then (1:ℝ) else 0)) =
        1+(Real.exp lam-1)*(if columnHit S c=false then 1 else 0) := by
    intro c
    cases columnHit S c <;> simp
  simp_rw [hmoment, mul_add, mul_one, mul_left_comm _ (Real.exp lam-1)]
  rw [Finset.sum_add_distrib, hnorm, ← Finset.mul_sum]
  have hz := columnHit_false_mass p S
  simp only [productMass,productMean,finiteMean,Set.mem_ofPred_eq] at hz
  congr 1
  congr 1
  convert hz using 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : columnHit S x=false <;> simp [hx]

lemma miss_probability_exp_bound {p : ℝ} (h1 : p ≤ 1) (s : ℕ) :
    (1-p)^s ≤ Real.exp (-p*s) := by
  have hb : 1-p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  calc
    (1-p)^s ≤ (Real.exp (-p))^s := pow_le_pow_left₀ (by linarith) hb s
    _=Real.exp (-p*s) := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma columnMiss_moment_bound {N : ℕ} {p : ℝ} (h1 : p ≤ 1)
    (S : Finset (Fin N)) :
    (∑ c : Fin N → Bool, productWeight (bernoulliWeight p) N c *
      Real.exp ((p*S.card)*(if columnHit S c=false then (1:ℝ) else 0)))  ≤  Real.exp 1 := by
  rw [columnMiss_exp_moment]
  have hz0 : 0 ≤ (1-p)^S.card := pow_nonneg (by linarith) _
  have hz := miss_probability_exp_bound h1 S.card
  have hmul := mul_le_mul_of_nonneg_right hz (Real.exp_pos (p*S.card)).le
  have he : Real.exp (-p*S.card)*Real.exp (p*S.card)=1 := by
    rw [← Real.exp_add]
    simp
  rw [he] at hmul
  have hexp := Real.add_one_le_exp (1:ℝ)
  nlinarith

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

noncomputable def columnHitCount {N : ℕ} (S : Finset (Fin N)) (c : Fin N → Fin N → Bool) : ℝ :=
  ∑ j, if columnHit S (c j)=true then 1 else 0

noncomputable def columnMissCount {N : ℕ} (S : Finset (Fin N)) (c : Fin N → Fin N → Bool) : ℝ :=
  ∑ j, if columnHit S (c j)=false then 1 else 0

lemma columnHit_add_miss {N : ℕ} (S : Finset (Fin N)) (c : Fin N → Fin N → Bool) :
    columnHitCount S c+columnMissCount S c=N := by
  classical
  unfold columnHitCount columnMissCount
  rw [← Finset.sum_add_distrib]
  have he : ∀ j, (if columnHit S (c j)=true then (1:ℝ) else 0)+
      (if columnHit S (c j)=false then 1 else 0)=1 := by
    intro j
    cases columnHit S (c j) <;> norm_num
  simp_rw [he]
  simp

lemma columnHitCount_moment {N : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (S : Finset (Fin N)) :
    productMean (productWeight (bernoulliWeight p) N) N
      (fun c => Real.exp (-columnHitCount S c)) ≤ Real.exp (-(N:ℝ)*(1-(1-p)^S.card)/2) := by
  classical
  have he : (fun c : Fin N → Fin N → Bool => Real.exp (-columnHitCount S c)) =
      (fun c => Real.exp (∑ j, -(if columnHit S (c j)=true then (1:ℝ) else 0))) := by
    funext c
    simp [columnHitCount, Finset.sum_neg_distrib]
  rw [he]
  rw [productMean_exp_sum (productWeight (bernoulliWeight p) N)
    (fun a : Fin N → Bool => -(if columnHit S a=true then (1:ℝ) else 0)) N]
  have hbase : 0 ≤ ∑ c : Fin N → Bool, productWeight (bernoulliWeight p) N c *
      Real.exp (-(if columnHit S c=true then (1:ℝ) else 0)) :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (productWeight_nonneg (bernoulliWeight_nonneg h0 h1) N c)
      (Real.exp_pos _).le)
  calc
    _ ≤ (Real.exp (-(1-(1-p)^S.card)/2))^N :=
      pow_le_pow_left₀ hbase (columnHit_moment_bound h0 h1 S) N
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma columnHitCount_lower_tail {N : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (S : Finset (Fin N)) (a : ℝ) :
    productMass (productWeight (bernoulliWeight p) N) N {c | columnHitCount S c<a} ≤
      Real.exp (a-(N:ℝ)*(1-(1-p)^S.card)/2) := by
  have hw := productWeight_nonneg (bernoulliWeight_nonneg h0 h1) N
  have hsub : {c : Fin N → Fin N → Bool | columnHitCount S c<a} ⊆
      {c | -a ≤ -columnHitCount S c} := by intro c hc; dsimp at *; linarith
  calc
    _ ≤ productMass (productWeight (bernoulliWeight p) N) N {c | -a ≤ -columnHitCount S c} :=
      productMass_mono hw hsub
    _ ≤ Real.exp (-(-a))*productMean (productWeight (bernoulliWeight p) N) N
        (fun c => Real.exp (-columnHitCount S c)) :=
      productMass_le_exp_moment _ hw N (fun c => -columnHitCount S c) (-a)
    _ ≤ Real.exp a*Real.exp (-(N:ℝ)*(1-(1-p)^S.card)/2) := by
      rw [neg_neg]
      exact mul_le_mul_of_nonneg_left (columnHitCount_moment h0 h1 S) (Real.exp_pos a).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma columnMissCount_moment {N : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (S : Finset (Fin N)) :
    productMean (productWeight (bernoulliWeight p) N) N
      (fun c => Real.exp ((p*S.card)*columnMissCount S c)) ≤ Real.exp N := by
  classical
  have he : (fun c : Fin N → Fin N → Bool => Real.exp ((p*S.card)*columnMissCount S c)) =
      (fun c => Real.exp (∑ j, (p*S.card)*(if columnHit S (c j)=false then (1:ℝ) else 0))) := by
    funext c
    simp only [columnMissCount, Finset.mul_sum]
  rw [he]
  rw [productMean_exp_sum (productWeight (bernoulliWeight p) N)
    (fun a : Fin N → Bool => (p*S.card)*(if columnHit S a=false then (1:ℝ) else 0)) N]
  have hbase : 0 ≤ ∑ c : Fin N → Bool, productWeight (bernoulliWeight p) N c *
      Real.exp ((p*S.card)*(if columnHit S c=false then (1:ℝ) else 0)) :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (productWeight_nonneg (bernoulliWeight_nonneg h0 h1) N c)
      (Real.exp_pos _).le)
  calc
    _ ≤ (Real.exp 1)^N := pow_le_pow_left₀ hbase (columnMiss_moment_bound h1 S) N
    _ = _ := by rw [← Real.exp_nat_mul]; simp

lemma columnMissCount_upper_tail {N : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (S : Finset (Fin N)) (a : ℝ) :
    productMass (productWeight (bernoulliWeight p) N) N {c | a ≤ columnMissCount S c} ≤
      Real.exp ((N:ℝ)-(p*S.card)*a) := by
  have hw := productWeight_nonneg (bernoulliWeight_nonneg h0 h1) N
  have hlam : 0 ≤ p*S.card := mul_nonneg h0 (Nat.cast_nonneg _)
  have hsub : {c : Fin N → Fin N → Bool | a ≤ columnMissCount S c} ⊆
      {c | (p*S.card)*a ≤ (p*S.card)*columnMissCount S c} :=
    fun _ hc => mul_le_mul_of_nonneg_left hc hlam
  calc
    _ ≤ productMass (productWeight (bernoulliWeight p) N) N
        {c | (p*S.card)*a ≤ (p*S.card)*columnMissCount S c} := productMass_mono hw hsub
    _ ≤ Real.exp (-((p*S.card)*a))*productMean (productWeight (bernoulliWeight p) N) N
        (fun c => Real.exp ((p*S.card)*columnMissCount S c)) :=
      productMass_le_exp_moment _ hw N (fun c => (p*S.card)*columnMissCount S c) ((p*S.card)*a)
    _ ≤ Real.exp (-((p*S.card)*a))*Real.exp N :=
      mul_le_mul_of_nonneg_left (columnMissCount_moment h0 h1 S) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

def boolRelation {N : ℕ} (x : Fin (N*N) → Bool) (i j : Fin N) : Prop :=
  x ((edgeEquiv N).symm (i,j))=true

lemma boolRelation_columns {N : ℕ} (c : Fin N → Fin N → Bool) (i j : Fin N) :
    boolRelation (columnsEquiv N c) i j ↔ c j i=true := by
  change c (edgeEquiv N ((edgeEquiv N).symm (i,j))).2
    (edgeEquiv N ((edgeEquiv N).symm (i,j))).1=true ↔ _
  rw [Equiv.apply_symm_apply]

lemma relNbhd_columns {N : ℕ} (S : Finset (Fin N)) (c : Fin N → Fin N → Bool) :
    relNbhd (boolRelation (columnsEquiv N c)) (S : Set (Fin N)) =
      (Finset.univ.filter (fun j => columnHit S (c j)=true) : Set (Fin N)) := by
  classical
  ext j
  simp [relNbhd,boolRelation_columns,columnHit]

lemma relNbhd_columns_card {N : ℕ} (S : Finset (Fin N)) (c : Fin N → Fin N → Bool) :
    ((relNbhd (boolRelation (columnsEquiv N c)) (S : Set (Fin N))).ncard : ℝ)=
      columnHitCount S c := by
  classical
  rw [relNbhd_columns,Set.ncard_coe_finset]
  simp only [Finset.card_filter,columnHitCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

def reindexEquiv {n : ℕ} {A : Type*} (e : Fin n ≃ Fin n) : (Fin n → A) ≃ (Fin n → A) where
  toFun x i := x (e i)
  invFun x i := x (e.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma productWeight_reindex {n : ℕ} {A : Type*} (w : A → ℝ) (e : Fin n ≃ Fin n) (x : Fin n → A) :
    productWeight w n (reindexEquiv e x)=productWeight w n x := by
  exact e.prod_comp (fun i => w (x i))

lemma productMass_reindex {n : ℕ} {A : Type*} [Fintype A]
    (w : A → ℝ) (e : Fin n ≃ Fin n) (B : Set (Fin n → A)) :
    productMass w n (reindexEquiv e ⁻¹' B)=productMass w n B := by
  classical
  unfold productMass productMean finiteMean
  simpa only [productWeight_reindex, Set.mem_preimage] using
    (reindexEquiv (A := A) e).sum_comp
      (fun x => productWeight w n x * if x ∈ B then (1:ℝ) else 0)

def transposeIndices (N : ℕ) : Fin (N*N) ≃ Fin (N*N) :=
  (edgeEquiv N).trans ((Equiv.prodComm (Fin N) (Fin N)).trans (edgeEquiv N).symm)

lemma boolRelation_transpose {N : ℕ} (x : Fin (N*N) → Bool) (i j : Fin N) :
    boolRelation (reindexEquiv (transposeIndices N) x) i j ↔ boolRelation x j i := by
  change x (transposeIndices N ((edgeEquiv N).symm (i,j)))=true ↔ _
  simp only [transposeIndices,Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.prodComm_apply]
  rfl

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment.ACFresh

lemma hit_probability_lower {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (s : ℕ)
    (hps : p*s ≤ 16) : p*s/17 ≤ 1-(1-p)^s := by
  let z := (1-p)^s
  have hz0 : 0 ≤ z := pow_nonneg (by linarith) _
  have hz1 : z ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hps0 : 0 ≤ p*s := mul_nonneg h0 (Nat.cast_nonneg _)
  have he := Real.add_one_le_exp (p*s)
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-p*s)).le
  have hexp : Real.exp (p*s)*Real.exp (-p*s)=1 := by
    rw [← Real.exp_add]
    simp
  rw [hexp] at hm
  have hz := miss_probability_exp_bound h1 s
  have hmul := mul_le_mul_of_nonneg_right hz (by linarith : 0 ≤ p*s+1)
  have hqprod := mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr hps)
  dsimp [z] at *
  nlinarith

lemma hit_probability_lower_scaled {N s : ℕ} (hN : 0 < N) {α p : ℝ}
    (hα : 0 ≤ α) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (hp : p*(N:ℝ)=128*α) (hs : α*s ≤ (N:ℝ)/8) :
    4*α*s ≤ (N:ℝ)*(1-(1-p)^s) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hscale : p*(N:ℝ)*s=128*α*s := by rw [hp]
  have hps : p*s ≤ 16 := by
    apply (mul_le_mul_iff_right₀ hN').mp
    nlinarith
  have h := hit_probability_lower h0 h1 s hps
  have hm := mul_le_mul_of_nonneg_left h hN'.le
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg s
  nlinarith [mul_nonneg hα hs0]

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment.ACFresh

def rowBad {N : ℕ} (α : ℝ) (S : Finset (Fin N)) : Set (Fin (N*N) → Bool) :=
  {x | ((relNbhd (boolRelation x) (S : Set (Fin N))).ncard : ℝ) <
    min (α*S.card) (3*(N:ℝ)/4)}

lemma rowBad_columns {N : ℕ} (α : ℝ) (S : Finset (Fin N)) :
    columnsEquiv N ⁻¹' rowBad α S =
      {c | columnHitCount S c < min (α*S.card) (3*(N:ℝ)/4)} := by
  ext c
  simp only [Set.mem_preimage,rowBad,Set.mem_ofPred_eq,relNbhd_columns_card]

lemma rowBad_mass {N : ℕ} (hN : 0 < N) {α p : ℝ} (hα : 0 ≤ α)
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp : p*(N:ℝ)=128*α)
    (S : Finset (Fin N)) :
    productMass (bernoulliWeight p) (N*N) (rowBad α S) ≤ Real.exp (-α*S.card) := by
  rw [productMass_columns,rowBad_columns]
  have hw := productWeight_nonneg (bernoulliWeight_nonneg h0 h1) N
  by_cases hs : α*S.card ≤ (N:ℝ)/8
  · have hsub : {c : Fin N → Fin N → Bool | columnHitCount S c < min (α*S.card) (3*(N:ℝ)/4)} ⊆
        {c | columnHitCount S c < α*S.card} := by
      intro c hc
      change columnHitCount S c < min (α*S.card) (3*(N:ℝ)/4) at hc
      change columnHitCount S c < α*S.card
      exact hc.trans_le (min_le_left _ _)
    have hq := hit_probability_lower_scaled hN hα h0 h1 hp hs
    calc
      _ ≤ productMass (productWeight (bernoulliWeight p) N) N {c | columnHitCount S c < α*S.card} :=
        productMass_mono hw hsub
      _ ≤ Real.exp (α*S.card-(N:ℝ)*(1-(1-p)^S.card)/2) := columnHitCount_lower_tail h0 h1 S _
      _ ≤ Real.exp (-α*S.card) := Real.exp_le_exp.mpr (by linarith)
  · have hsub : {c : Fin N → Fin N → Bool | columnHitCount S c < min (α*S.card) (3*(N:ℝ)/4)} ⊆
        {c | (N:ℝ)/4 ≤ columnMissCount S c} := by
      intro c hc
      change columnHitCount S c < min (α*S.card) (3*(N:ℝ)/4) at hc
      change (N:ℝ)/4 ≤ columnMissCount S c
      have hh := hc.trans_le (min_le_right _ _)
      have he := columnHit_add_miss S c
      linarith
    have hmul : p*(N:ℝ)*S.card=128*α*S.card := by rw [hp]
    calc
      _ ≤ productMass (productWeight (bernoulliWeight p) N) N {c | (N:ℝ)/4 ≤ columnMissCount S c} :=
        productMass_mono hw hsub
      _ ≤ Real.exp ((N:ℝ)-(p*S.card)*((N:ℝ)/4)) := columnMissCount_upper_tail h0 h1 S _
      _ ≤ Real.exp (-α*S.card) := Real.exp_le_exp.mpr (by nlinarith)

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

def forwardBad (N : ℕ) (α : ℝ) : Set (Fin (N*N) → Bool) :=
  {x | ¬strongGrowth N α (boolRelation x)}

def expansionBad (N : ℕ) (α : ℝ) : Set (Fin (N*N) → Bool) :=
  forwardBad N α ∪ reindexEquiv (transposeIndices N) ⁻¹' forwardBad N α

lemma forwardBad_subset_union (N : ℕ) (α : ℝ) :
    forwardBad N α ⊆ {x | ∃ S ∈ (Finset.univ : Finset (Fin N)).powerset, x ∈ rowBad α S} := by
  classical
  intro x hx
  change ¬∀ S : Set (Fin N), _ at hx
  push Not at hx
  obtain ⟨S,hS⟩ := hx
  refine ⟨S.toFinset, by simp, ?_⟩
  simpa only [rowBad,Set.mem_ofPred_eq,Set.coe_toFinset,Set.ncard_eq_toFinset_card'] using hS

lemma rowBad_empty (N : ℕ) (α : ℝ) : rowBad (N := N) α ∅=∅ := by
  ext x
  have hN : (0:ℝ) ≤ 3*(N:ℝ)/4 := by positivity
  simp [rowBad,relNbhd,min_eq_left hN]

lemma rowBad_mass_card {N : ℕ} (hN : 0 < N) {α p : ℝ} (hα : 0 ≤ α)
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp : p*(N:ℝ)=128*α)
    (S : Finset (Fin N)) :
    productMass (bernoulliWeight p) (N*N) (rowBad α S) ≤
      if S.card=0 then 0 else Real.exp (-α*S.card) := by
  classical
  by_cases hS : S.card=0
  · have he : S=∅ := Finset.card_eq_zero.mp hS
    subst S
    rw [rowBad_empty]
    simp [productMass,productMean,finiteMean]
  · rw [if_neg hS]
    exact rowBad_mass hN hα h0 h1 hp S

lemma row_subset_sum (N : ℕ) (α : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
      if S.card=0 then (0:ℝ) else Real.exp (-α*S.card)) =
      ∑ s ∈ Finset.range (N+1), if s=0 then 0 else (N.choose s:ℝ)*Real.exp (-α*s) := by
  classical
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_powersetCard s (Finset.univ : Finset (Fin N))
    (fun k => if k=0 then (0:ℝ) else Real.exp (-α*k))]
  simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  split_ifs <;> simp_all

lemma forwardBad_mass_of_series {N : ℕ} (hN : 0 < N) {α p : ℝ} (hα : 0 ≤ α)
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp : p*(N:ℝ)=128*α)
    (hseries : (∑ s ∈ Finset.range (N+1), if s=0 then (0:ℝ) else
      (N.choose s:ℝ)*Real.exp (-α*s)) ≤ 2*Real.exp (-α/2)) :
    productMass (bernoulliWeight p) (N*N) (forwardBad N α) ≤ 2*Real.exp (-α/2) := by
  classical
  calc
    _ ≤ productMass (bernoulliWeight p) (N*N)
        {x | ∃ S ∈ (Finset.univ : Finset (Fin N)).powerset, x ∈ rowBad α S} :=
      productMass_mono (bernoulliWeight_nonneg h0 h1) (forwardBad_subset_union N α)
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
        productMass (bernoulliWeight p) (N*N) (rowBad α S) :=
      productMass_finite_union _ (bernoulliWeight_nonneg h0 h1) _ _ _
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
        if S.card=0 then 0 else Real.exp (-α*S.card) :=
      Finset.sum_le_sum (fun S _ => rowBad_mass_card hN hα h0 h1 hp S)
    _ = _ := row_subset_sum N α
    _ ≤ _ := hseries

lemma productMass_union_le {A : Type*} [Fintype A] (w : A → ℝ) (hw : ∀ a,0 ≤ w a)
    (n : ℕ) (B C : Set (Fin n → A)) :
    productMass w n (B∪C) ≤ productMass w n B+productMass w n C := by
  classical
  unfold productMass productMean finiteMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hx := productWeight_nonneg hw n x
  by_cases hb : x ∈ B <;> by_cases hc : x ∈ C <;> simp [hb,hc]
  linarith

lemma expansionBad_mass_of_series {N : ℕ} (hN : 0 < N) {α p : ℝ} (hα : 0 ≤ α)
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp : p*(N:ℝ)=128*α)
    (hseries : (∑ s ∈ Finset.range (N+1), if s=0 then (0:ℝ) else
      (N.choose s:ℝ)*Real.exp (-α*s)) ≤ 2*Real.exp (-α/2)) :
    productMass (bernoulliWeight p) (N*N) (expansionBad N α) ≤ 4*Real.exp (-α/2) := by
  have h := forwardBad_mass_of_series hN hα h0 h1 hp hseries
  have hu := productMass_union_le (bernoulliWeight p) (bernoulliWeight_nonneg h0 h1) (N*N)
    (forwardBad N α) (reindexEquiv (transposeIndices N) ⁻¹' forwardBad N α)
  rw [productMass_reindex] at hu
  change productMass (bernoulliWeight p) (N*N) (expansionBad N α) ≤ _ at hu
  linarith

lemma not_expansionBad_growth {N : ℕ} {α : ℝ} {x : Fin (N*N) → Bool}
    (hx : x ∉ expansionBad N α) :
    strongGrowth N α (boolRelation x) ∧ strongGrowth N α (fun i j => boolRelation x j i) := by
  classical
  have hh : x ∉ forwardBad N α ∧ reindexEquiv (transposeIndices N) x ∉ forwardBad N α := by
    simpa only [expansionBad,Set.mem_union,Set.mem_preimage,not_or] using hx
  constructor
  · simpa only [forwardBad,Set.mem_ofPred_eq,not_not] using hh.1
  · have he : (fun i j => boolRelation x j i)=boolRelation (reindexEquiv (transposeIndices N) x) := by
      funext i j
      exact propext (boolRelation_transpose x i j).symm
    rw [he]
    simpa only [forwardBad,Set.mem_ofPred_eq,not_not] using hh.2

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal BigOperators
namespace TalagrandConc.Assignment.ACFresh

noncomputable def unitThreshold (p : ℝ) (x : unitInterval) : Bool := if (x:ℝ) ≤ p then true else false

lemma measurable_unitThreshold (p : ℝ) : Measurable (unitThreshold p) := by
  apply Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
  · exact measurable_const
  · exact measurable_const

lemma unitThreshold_atom {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Bool) :
    (volume : Measure unitInterval) {x | unitThreshold p x=b}=ENNReal.ofReal (bernoulliWeight p b) := by
  let z : unitInterval := ⟨p,h0,h1⟩
  cases b
  · have he : {x | unitThreshold p x=false}=Set.Ioi z := by
      ext x
      simp [unitThreshold,z,not_le]
      rfl
    rw [he,unitInterval.volume_Ioi]
    rfl
  · have he : {x | unitThreshold p x=true}=Set.Iic z := by
      ext x
      simp [unitThreshold,z]
      rfl
    rw [he,unitInterval.volume_Iic]
    rfl

lemma thresholdSample_cubeLift (N : ℕ) (p : ℝ) (x : Fin (N*N) → unitInterval) :
    thresholdSample N p (cubeLift N x)=quantizedPoint (unitThreshold p) x := by
  ext i
  simp only [thresholdSample,cubeLift,Equiv.symm_apply_apply,quantizedPoint,unitThreshold]
  split_ifs <;> simp_all

lemma measurable_thresholdSample (N : ℕ) (p : ℝ) : Measurable (thresholdSample N p) := by
  apply measurable_pi_lambda
  intro i
  have he : (fun X : Fin N × Fin N → ℝ => decide (X (edgeEquiv N i)≤p))=
      (fun X => if X (edgeEquiv N i)≤p then true else false) := by
    funext X
    split_ifs <;> simp_all
  rw [show (fun X => thresholdSample N p X i)=_ from he]
  exact Measurable.ite (measurableSet_le (measurable_pi_apply _) measurable_const)
    measurable_const measurable_const

lemma costLaw_threshold_mass (N : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (B : Set (Fin (N*N) → Bool)) :
    costLaw N (thresholdSample N p ⁻¹' B)=
      ENNReal.ofReal (productMass (bernoulliWeight p) (N*N) B) := by
  have hB : MeasurableSet B := Set.toFinite B |>.measurableSet
  rw [← (cubeLift_preserving N).map_eq,Measure.map_apply (cubeLift_preserving N).measurable
    ((measurable_thresholdSample N p) hB)]
  have he : cubeLift N ⁻¹' (thresholdSample N p ⁻¹' B)=
      quantizedPoint (unitThreshold p) ⁻¹' B := by
    ext x
    simp only [Set.mem_preimage,thresholdSample_cubeLift]
  rw [he]
  exact cube_quantized_mass (unitThreshold p) (measurable_unitThreshold p)
    (bernoulliWeight p) (bernoulliWeight_nonneg h0 h1) (unitThreshold_atom h0 h1) (N*N) B

end TalagrandConc.Assignment.ACFresh
end

section

open scoped BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma optimal_edge_le_exchange {N : ℕ} {X : Fin N × Fin N → ℝ}
    (hX : ∀ p, 0 ≤ X p) {τ : Equiv.Perm (Fin N)} (hτ : IsOptimalAssignment X τ)
    (π : Equiv.Perm (Fin N)) (F : Finset (Fin N)) {p : ℝ}
    (hfix : ∀ j, j ∉ F → π j=j) (hcheap : ∀ j ∈ F, X (j,τ (π j)) ≤ p)
    {i : Fin N} (hi : i ∈ F) : X (i,τ i) ≤ F.card*p := by
  classical
  have hopt := hτ (π.trans τ)
  change (∑ j, X (j,τ j))  ≤  ∑ j, X (j,τ (π j)) at hopt
  rw [← F.sum_add_sum_compl (fun j => X (j,τ j)),
    ← F.sum_add_sum_compl (fun j => X (j,τ (π j)))] at hopt
  have hcomp : (∑ j ∈ Fᶜ, X (j,τ (π j))) = ∑ j ∈ Fᶜ, X (j,τ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hfix j (Finset.mem_compl.mp hj)]
  rw [hcomp] at hopt
  have hf : (∑ j ∈ F, X (j,τ j)) ≤ ∑ j ∈ F, X (j,τ (π j)) := by linarith
  calc
    X (i,τ i)  ≤  ∑ j ∈ F, X (j,τ j) := Finset.single_le_sum (fun j _ => hX (j,τ j)) hi
    _  ≤  ∑ j ∈ F, X (j,τ (π j)) := hf
    _  ≤  ∑ _j ∈ F, p := Finset.sum_le_sum hcheap
    _ = F.card*p := by simp

lemma closedWalk_rotate_value {V : Type*} {n : ℕ} (hn : 0  <  n) {c : ℕ → V}
    (hclose : c n=c 0) (j : Fin n) : c (finRotate n j).val=c (j.val+1) := by
  cases n with
  | zero => omega
  | succ n =>
    by_cases hj : j=Fin.last n
    · subst j
      simpa using hclose.symm
    · rw [coe_finRotate_of_ne_last hj]

lemma optimal_edge_le_simple_cycle {N n : ℕ} {X : Fin N × Fin N → ℝ}
    (hX : ∀ p, 0 ≤ X p) {τ : Equiv.Perm (Fin N)} (hτ : IsOptimalAssignment X τ)
    {p : ℝ} {i : Fin N} {c : ℕ → Fin N}
    (hc : ClosedWalk (fun x y => X (x,τ y) ≤ p) i n c)
    (hinj : ∀ a b, a < n → b < n → c a=c b → a=b) : X (i,τ i) ≤ n*p := by
  classical
  let e : Fin n ↪ Fin N := ⟨fun j => c j.val, fun a b h => Fin.ext (hinj _ _ a.isLt b.isLt h)⟩
  let π : Equiv.Perm (Fin N) := (finRotate n).viaFintypeEmbedding e
  let F : Finset (Fin N) := Finset.univ.image e
  have hF : F.card=n := by simp [F,Finset.card_image_of_injective _ e.injective]
  have hi : i ∈ F := by
    apply Finset.mem_image.mpr
    exact ⟨⟨0,hc.1⟩,Finset.mem_univ _,hc.2.1⟩
  have hfix : ∀ j, j ∉ F → π j=j := by
    intro j hj
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
    rintro ⟨a,rfl⟩
    exact hj (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  have hcheap : ∀ j ∈ F, X (j,τ (π j)) ≤ p := by
    intro j hj
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hj
    change X (e a,τ ((finRotate n).viaFintypeEmbedding e (e a))) ≤ p
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image]
    change X (c a.val,τ (c (finRotate n a).val)) ≤ p
    rw [closedWalk_rotate_value hc.1 (hc.2.2.1.trans hc.2.1.symm)]
    exact hc.2.2.2 a.val a.isLt
  simpa [hF] using optimal_edge_le_exchange hX hτ π F hfix hcheap hi

lemma optimal_edge_le_strong_growth {N : ℕ} (hN : 3 ≤ N) {α p : ℝ}
    (hα : 3 ≤ α) (hp : 0 ≤ p) {X : Fin N × Fin N → ℝ}
    (hX : ∀ q, 0 ≤ X q)
    (hD : smallGrowth N α (fun x y => X (x,y) ≤ p))
    (hDr : smallGrowth N α (fun x y => X (y,x) ≤ p))
    {m : ℕ} (hm : 0  <  m) (hpow : (N:ℝ) < α^m)
    (τ : Equiv.Perm (Fin N)) (hτ : IsOptimalAssignment X τ) (i : Fin N) :
    X (i,τ i) ≤ 2*(m:ℝ)*p := by
  obtain ⟨n,_,hn,c,hc,hinj⟩ := smallGrowth_simple_alternating_cycle (D := {q : Fin N × Fin N | X q ≤ p}) hN hα hD hDr hm hpow τ i
  have hedge := optimal_edge_le_simple_cycle hX hτ hc hinj
  have hn' : (n:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hn
  exact hedge.trans (mul_le_mul_of_nonneg_right hn' hp)

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment.ACFresh

lemma capped_threshold_relation {N : ℕ} {p b : ℝ} (hpb : p<b)
    (X : Fin N × Fin N → ℝ) :
    (fun x y : Fin N => cappedCosts b X (x,y) ≤ p) = (fun x y => X (x,y) ≤ p) := by
  funext x y
  apply propext
  exact min_le_iff.trans (or_iff_left (not_le_of_gt hpb))

lemma cap_optCost_eq_strongGrowth {N : ℕ} (hN : 3 ≤ N) {α p b : ℝ}
    (hα : 3 ≤ α) (hp : 0 ≤ p) {X : Fin N × Fin N → ℝ}
    (hX : ∀ q, 0 ≤ X q)
    (hD : smallGrowth N α (fun x y => X (x,y) ≤ p))
    (hDr : smallGrowth N α (fun x y => X (y,x) ≤ p))
    {m : ℕ} (hm : 0 < m) (hpow : (N:ℝ) < α^m)
    (hpb : p < b) (hvb : 2*m*p < b) :
    optCost (cappedCosts b X)=optCost X := by
  apply capped_optCost_eq_of_optimal_below hvb X
  intro τ hτ i
  apply optimal_edge_le_strong_growth hN hα hp
    (fun q => le_min (hX q) (hp.trans hpb.le)) ?_ ?_ hm hpow τ hτ i
  · change smallGrowth N α (fun x y => cappedCosts b X (x,y) ≤ p)
    rw [capped_threshold_relation hpb]
    exact hD
  · have he : (fun x y : Fin N => cappedCosts b X (y,x) ≤ p) =
        (fun x y => X (y,x) ≤ p) := by
      funext x y
      apply propext
      exact min_le_iff.trans (or_iff_left (not_le_of_gt hpb))
    change smallGrowth N α (fun x y => cappedCosts b X (y,x) ≤ p)
    rw [he]
    exact hDr

lemma doubled_cap_optCost_eq {N : ℕ} (hN : 3 ≤ N) {α p : ℝ}
    (hα : 3 ≤ α) (hp : 0 < p) {X : Fin N × Fin N → ℝ}
    (hX : ∀ q, 0 ≤ X q)
    (hD : smallGrowth N α (fun x y => X (x,y) ≤ p))
    (hDr : smallGrowth N α (fun x y => X (y,x) ≤ p))
    {m : ℕ} (hm : 0 < m) (hpow : (N:ℝ) < α^m) :
    optCost (cappedCosts (4*m*p) X)=optCost X := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  apply cap_optCost_eq_strongGrowth hN hα hp.le hX hD hDr hm hpow <;> nlinarith

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal BigOperators

namespace TalagrandConc.Assignment.ACFresh

lemma boolRelation_threshold {N : ℕ} (p : ℝ) (X : Fin N × Fin N → ℝ) :
    boolRelation (thresholdSample N p X) = (fun i j => X (i,j) ≤ p) := by
  funext i j
  apply propext
  change decide (X (edgeEquiv N ((edgeEquiv N).symm (i,j))) ≤ p)=true ↔ _
  rw [Equiv.apply_symm_apply]
  simp

lemma native_outside_expansionBad {N : ℕ} (hN : 3 ≤ N) {α p : ℝ}
    (hα : 3 ≤ α) (hp : 0 < p) {m : ℕ} (hm : 0 < m) (hpow : (N:ℝ) < α^m)
    (X : Fin N × Fin N → ℝ) (hX : ∀ q,0 ≤ X q)
    (hx : thresholdSample N p X ∉ expansionBad N α) :
    optCost (cappedCosts (4*m*p) X)=optCost X := by
  obtain ⟨hf,hb⟩ := not_expansionBad_growth hx
  rw [boolRelation_threshold] at hf
  have hbe : (fun i j => boolRelation (thresholdSample N p X) j i) =
      (fun i j => X (j,i) ≤ p) := by rw [boolRelation_threshold]
  rw [hbe] at hb
  exact doubled_cap_optCost_eq hN hα hp hX (fun S _ => hf S) (fun S _ => hb S) hm hpow

lemma cappedCosts_eq_of_bound {N : ℕ} {b : ℝ} (X : Fin N × Fin N → ℝ)
    (hX : ∀ q,X q ≤ b) : cappedCosts b X=X := by
  funext q
  exact min_eq_left (hX q)

lemma exists_native_expansion_exception {N : ℕ} (hN : 3 ≤ N) {α p : ℝ}
    (hα : 3 ≤ α) (hp : 0 < p) (hscale : p*(N:ℝ)=128*α)
    {m : ℕ} (hm : 0 < m) (hpow : (N:ℝ) < α^m)
    (hseries : (∑ s ∈ Finset.range (N+1), if s=0 then (0:ℝ) else
      (N.choose s:ℝ)*Real.exp (-α*s)) ≤ 2*Real.exp (-α/2)) :
    ∃ E : Set (Fin N × Fin N → ℝ), MeasurableSet E ∧
      costLaw N E ≤ ENNReal.ofReal (4*Real.exp (-α/2)) ∧
      ∀ X, (∀ q,X q ∈ Set.Icc (0:ℝ) 1) → X ∉ E →
        optCost (cappedCosts (4*m*p) X)=optCost X := by
  classical
  by_cases hp1 : p ≤ 1
  · let E := thresholdSample N p ⁻¹' expansionBad N α
    refine ⟨E, (measurable_thresholdSample N p) (Set.toFinite _ |>.measurableSet), ?_, ?_⟩
    · change costLaw N (thresholdSample N p ⁻¹' expansionBad N α) ≤ _
      rw [costLaw_threshold_mass N hp.le hp1]
      exact ENNReal.ofReal_le_ofReal (expansionBad_mass_of_series (by omega : 0 < N)
        (by linarith : 0 ≤ α) hp.le hp1 hscale hseries)
    · intro X hX hx
      exact native_outside_expansionBad hN hα hp hm hpow X (fun q => (hX q).1) hx
  · refine ⟨∅,MeasurableSet.empty,by simp,?_⟩
    intro X hX _
    have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hb : 1 ≤ 4*(m:ℝ)*p := by nlinarith
    rw [cappedCosts_eq_of_bound X (fun q => (hX q).2.trans hb)]

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal
namespace TalagrandConc.Assignment.ACFresh

lemma lift_native_bad_event {N : ℕ} {b q : ℝ}
    {E : Set (Fin N × Fin N → ℝ)} (hEm : MeasurableSet E)
    (hE : costLaw N E ≤ ENNReal.ofReal q)
    (heq : ∀ X ∉ E, (∀ p, X p ∈ Set.Icc (0:ℝ) 1) → optCost (cappedCosts b X)=optCost X) :
    ∃ F : Set (Fin (N*N) → unitInterval), cubeLaw (N*N) F ≤ ENNReal.ofReal q ∧
      ∀ x ∉ F, cappedObservable N b x=originalObservable N x := by
  refine ⟨cubeLift N ⁻¹' E,?_,?_⟩
  · rw [← (cubeLift_preserving N).map_eq,Measure.map_apply (cubeLift_preserving N).measurable hEm] at hE
    exact hE
  · intro x hx
    exact heq (cubeLift N x) hx (fun p => (x ((edgeEquiv N).symm p)).property)

end TalagrandConc.Assignment.ACFresh
end

section

open MeasureTheory
open scoped ENNReal BigOperators
namespace TalagrandConc.Assignment.ACFresh

lemma parameter_bad_event_of_series (N : ℕ) (hN : 3 ≤ N) (t : ℝ)
    (hseries : (∑ s ∈ Finset.range (N+1), if s=0 then (0:ℝ) else
      (N.choose s:ℝ)*Real.exp (-expansionAlpha N t*s)) ≤
        2*Real.exp (-expansionAlpha N t/2)) :
    ∃ E : Set (Fin (N*N) → unitInterval),
      cubeLaw (N*N) E ≤ ENNReal.ofReal (4*Real.exp (-expansionAlpha N t/2)) ∧
      ∀ x ∉ E, cappedObservable N (capSize N t) x=originalObservable N x := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have ha : 3 ≤ expansionAlpha N t := by linarith [alpha_ge_sixtyfour N hN t]
  let p : ℝ := 128*expansionAlpha N t/N
  have hp : 0 < p := by dsimp [p]; positivity
  have hscale : p*(N:ℝ)=128*expansionAlpha N t := by dsimp [p]; field_simp
  obtain ⟨E,hEm,hE,heq⟩ := exists_native_expansion_exception hN ha hp hscale
    (by have := cycleLength_pos N t; omega : 0 < cycleLength N t)
    (alpha_pow_cycleLength N hN t) hseries
  have hcap : 4*(cycleLength N t:ℝ)*p=capSize N t := by dsimp [p,capSize]; ring
  rw [hcap] at heq
  exact lift_native_bad_event hEm hE (fun X hx hX => heq X hX hx)

end TalagrandConc.Assignment.ACFresh
end

section
open scoped BigOperators
namespace TalagrandConc.Assignment.ACFresh

lemma positive_geometric_sum_bound (N : ℕ) (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) :
    (∑ s ∈ Finset.range (N+1), if s=0 then 0 else r^s) ≤ 2*r := by
  have hg : (∑ s ∈ Finset.range N, r^s) ≤ 2 := by
    apply le_trans (Finset.sum_le_sum (fun s _ => pow_le_pow_left₀ hr hrhalf s))
    exact sum_geometric_two_le N
  calc
    _ = (∑ s ∈ Finset.range N, r^s)*r := by
      rw [Finset.sum_range_succ']
      simp [pow_succ,Finset.sum_mul]
    _ ≤ 2*r := mul_le_mul_of_nonneg_right hg hr

lemma assignment_power_exp_sum (N : ℕ) (hN : 3 ≤ N) (a : ℝ)
    (ha : 64*Real.log (N:ℝ) ≤ a) :
    (∑ s ∈ Finset.range (N+1), if s=0 then 0 else
      (N:ℝ)^s*Real.exp (-a*(s:ℝ))) ≤ 2*Real.exp (-a/2) := by
  have hn : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl := assignment_log_gt_one N hN
  have ha2 : Real.log (N:ℝ) ≤ a/2 := by linarith
  have hr : Real.exp (-a/2) ≤ 1/2 := by
    have hlog2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 1/2 := by rw [Real.exp_neg,Real.exp_log (by norm_num),one_div]
  have hpoint (s : ℕ) : (N:ℝ)^s*Real.exp (-a*(s:ℝ)) ≤ (Real.exp (-a/2))^s := by
    calc
      _ = Real.exp ((s:ℝ)*Real.log (N:ℝ))*Real.exp (-a*(s:ℝ)) := by
        rw [Real.exp_nat_mul,Real.exp_log hn]
      _ = Real.exp ((s:ℝ)*Real.log (N:ℝ)-a*(s:ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((s:ℝ)*(-a/2)) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left ha2 (Nat.cast_nonneg s : (0:ℝ) ≤ s)
        nlinarith
      _ = _ := Real.exp_nat_mul _ _
  apply le_trans (Finset.sum_le_sum (fun s _ => ?_))
    (positive_geometric_sum_bound N (Real.exp (-a/2)) (Real.exp_pos _).le hr)
  split_ifs with hs
  · exact le_rfl
  · exact hpoint s

lemma assignment_choose_exp_sum (N : ℕ) (hN : 3 ≤ N) (a : ℝ)
    (ha : 64*Real.log (N:ℝ) ≤ a) :
    (∑ s ∈ Finset.range (N+1), if s=0 then 0 else
      (N.choose s:ℝ)*Real.exp (-a*(s:ℝ))) ≤ 2*Real.exp (-a/2) := by
  apply le_trans (Finset.sum_le_sum (fun s _ => ?_)) (assignment_power_exp_sum N hN a ha)
  split_ifs with hs
  · exact le_rfl
  · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact_mod_cast Nat.choose_le_pow N s

end TalagrandConc.Assignment.ACFresh
end

section

namespace TalagrandConc.Assignment

open MeasureTheory

/-- Talagrand (1995), p. 169, Theorem 10.5. There is a universal constant `K > 0` such that
for every `N ≥ 3`, every median `M` of the optimal assignment cost `L_N` (costs i.i.d.
uniform on `[0, 1]`) and every `t ≥ 0`:
(10.7) if `t ≤ √(log N)` then `P(|L_N − M| ≥ K t (log N)² / (√N log log N)) ≤ 2 exp(−t²)`;
(10.8) if `t ≥ √(log N)` then `P(|L_N − M| ≥ K t³ log N / (√N log t²)) ≤ 2 exp(−t²)`. -/
theorem theorem_10_5 :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 3 ≤ N → ∀ M : ℝ, TalagrandConc.BinPacking.IsMedian (costLaw N) optCost M →
      ∀ t : ℝ, 0 ≤ t →
        (t ≤ Real.sqrt (Real.log N) →
          costLaw N {X | K * t * Real.log N ^ 2 / (Real.sqrt N * Real.log (Real.log N)) ≤
              |optCost X - M|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2))) ∧
        (Real.sqrt (Real.log N) ≤ t →
          costLaw N {X | K * t ^ 3 * Real.log N / (Real.sqrt N * Real.log (t ^ 2)) ≤
              |optCost X - M|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)))  := by
  apply ACFresh.native_concentration_of_scales
  intro N hN M t ht htlarge hM
  obtain ⟨E,hE,heq⟩ := ACFresh.parameter_bad_event_of_series N hN t
    (ACFresh.assignment_choose_exp_sum N hN (ACFresh.expansionAlpha N t) (ACFresh.alpha_ge_log N t))
  exact ACFresh.native_single_scale hN ht htlarge hM hE heq

end TalagrandConc.Assignment
end

open TalagrandConc.Assignment

theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 3 ≤ N → ∀ M : ℝ, TalagrandConc.BinPacking.IsMedian (costLaw N) optCost M →
      ∀ t : ℝ, 0 ≤ t →
        (t ≤ Real.sqrt (Real.log N) →
          costLaw N {X | K * t * Real.log N ^ 2 / (Real.sqrt N * Real.log (Real.log N)) ≤
              |optCost X - M|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2))) ∧
        (Real.sqrt (Real.log N) ≤ t →
          costLaw N {X | K * t ^ 3 * Real.log N / (Real.sqrt N * Real.log (t ^ 2)) ≤
              |optCost X - M|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2))) :=
  TalagrandConc.Assignment.theorem_10_5
