-- Prove2me | solution 1 for TalagrandConc.Chromatic.theorem_9_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T06:01:52.447318+00:00
-- url     : https://prove2.me/submissions/af221556-80d7-4bb0-9d10-c90afd4033bc

import Mathlib
import Definitions.Def_TalagrandConc_Chromatic_Basic

open MeasureTheory
open scoped Classical

section

open scoped BigOperators
open MeasureTheory

namespace TalagrandConc.Chromatic.Fresh

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

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

end TalagrandConc.Chromatic.Fresh
end

section

namespace TalagrandConc.Chromatic.Fresh

abbrev Rows (n : ℕ) := Fin n → (Fin n → Bool)

def rowEdges {n : ℕ} (x : Rows n) : EdgeSlot n → Bool :=
  fun e => x e.val.2 e.val.1

def rowGraph {n : ℕ} (x : Rows n) : SimpleGraph (Fin n) := graphOf (rowEdges x)

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

lemma indicator_sqNorm {n : ℕ} (H : Finset (Fin n)) :
    sqNorm (fun i => if i ∈ H then (1:ℝ) else 0) = H.card := by
  classical
  simp [sqNorm]

lemma indicator_mismatch_sum {α : Type*} [DecidableEq α] {n : ℕ}
    (x y : Fin n → α) (H : Finset (Fin n)) :
    (∑ i, if x i = y i then (0:ℝ) else if i ∈ H then 1 else 0) =
      ((H.filter fun i => x i ≠ y i).card : ℝ) := by
  classical
  rw [Finset.card_filter, Nat.cast_sum]
  calc
    _ = ∑ i ∈ H, if x i = y i then (0:ℝ) else if i ∈ H then 1 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ H)
      intro i _ hi
      simp [hi]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hxy : x i = y i <;> simp [hi,hxy]

lemma distance_subset_witness {α : Type*} [DecidableEq α] {n m : ℕ}
    {A : Set (Fin n → α)} (hA : A.Nonempty) (x : Fin n → α)
    {t : ℝ} (ht : 0 ≤ t) (hd : convexDistanceSq A x ≤ t^2)
    (H : Finset (Fin n)) (hH : H.card = m) :
    ∃ y ∈ A, ((H.filter fun i => x i ≠ y i).card : ℝ) ≤ t*Real.sqrt m := by
  classical
  obtain ⟨y,hy,hw⟩ := convexDistance_weight_witness hA x
    (fun i => if i ∈ H then (1:ℝ) else 0) (by intro i; split_ifs <;> norm_num)
  rw [indicator_sqNorm,indicator_mismatch_sum,hH] at hw
  have hs : Real.sqrt (convexDistanceSq A x) ≤ t := by
    simpa only [Real.sqrt_sq ht] using Real.sqrt_le_sqrt hd
  refine ⟨y,hy,hw.trans ?_⟩
  nlinarith [Real.sqrt_nonneg (m:ℝ)]

end TalagrandConc.Chromatic.Fresh
end

section
noncomputable section
open MeasureTheory
open scoped Classical
namespace TalagrandConc.Chromatic.Fresh

lemma chiSet_le_card {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    chiSet G A ≤ A.card := by
  have h := (G.induce (A : Set (Fin n))).colorable_of_fintype.chromaticNumber_le
  have hc : Fintype.card ↥(A : Set (Fin n)) = A.card := Fintype.card_coe A
  simpa only [hc, chiSet] using h

lemma chiSet_ne_top {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    chiSet G A ≠ ⊤ := ne_of_lt ((chiSet_le_card G A).trans_lt (ENat.natCast_lt_top _))

lemma chiM_le_chiSet {n m : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (hA : A.card = m) : chiM G m ≤ chiSet G A :=
  iInf_le_of_le A (iInf_le_of_le hA le_rfl)

lemma exists_card_subset {n m : ℕ} (hm : m ≤ n) :
    ∃ A : Finset (Fin n), A.card = m := by
  obtain ⟨A, _, hA⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (n := m)
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hm)
  exact ⟨A, hA⟩

lemma chiM_le_m {n m : ℕ} (G : SimpleGraph (Fin n)) (hm : m ≤ n) :
    chiM G m ≤ m := by
  obtain ⟨A, hA⟩ := exists_card_subset hm
  exact (chiM_le_chiSet G A hA).trans (hA ▸ chiSet_le_card G A)

lemma chiM_ne_top {n m : ℕ} (G : SimpleGraph (Fin n)) (hm : m ≤ n) :
    chiM G m ≠ ⊤ := ne_of_lt ((chiM_le_m G hm).trans_lt (ENat.natCast_lt_top _))

def chiNat {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : ℕ := (chiM G m).toNat

lemma chiNat_cast {n m : ℕ} (G : SimpleGraph (Fin n)) (hm : m ≤ n) :
    (chiNat G m : ℕ∞) = chiM G m := ENat.natCast_toNat (chiM_ne_top G hm)

lemma chiNat_le {n m : ℕ} (G : SimpleGraph (Fin n)) (hm : m ≤ n) :
    chiNat G m ≤ m := ENat.toNat_le_of_le_natCast (chiM_le_m G hm)

lemma chiMZ_eq {n m : ℕ} (G : SimpleGraph (Fin n)) (hm : m ≤ n) :
    chiMZ G m = ((chiNat G m : ℤ) : WithTop ℤ) := by
  rw [chiMZ, ← chiNat_cast G hm]
  rfl

lemma chiSet_natCast {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    ((chiSet G A).toNat : ℕ∞) = chiSet G A := ENat.natCast_toNat (chiSet_ne_top G A)

lemma chiSet_colorable {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    (G.induce (A : Set (Fin n))).Colorable (chiSet G A).toNat :=
  (G.induce (A : Set (Fin n))).colorable_chromaticNumber_of_fintype

end TalagrandConc.Chromatic.Fresh
end

section
noncomputable section
open scoped Classical
namespace TalagrandConc.Chromatic.Fresh

lemma colorable_splice {n r k : ℕ} (G H : SimpleGraph (Fin n))
    (A F : Finset (Fin n)) (hG : (G.induce (A : Set (Fin n))).Colorable r)
    (hF : (H.induce (F : Set (Fin n))).Colorable k)
    (hag : ∀ u ∈ A, ∀ v ∈ A, u ∉ F → v ∉ F → H.Adj u v → G.Adj u v) :
    (H.induce (A : Set (Fin n))).Colorable (r + k) := by
  obtain ⟨CG⟩ := hG
  obtain ⟨CF⟩ := hF
  let color : ↥(A : Set (Fin n)) → (Fin r ⊕ Fin k) := fun v =>
    if hv : v.val ∈ F then Sum.inr (CF ⟨v.val, hv⟩) else Sum.inl (CG v)
  have hvalid : ∀ {u v : (A : Set (Fin n))}, (H.induce (A : Set (Fin n))).Adj u v →
      color u ≠ color v := by
    intro u v huv
    change H.Adj u.val v.val at huv
    by_cases hu : u.val ∈ F
    · by_cases hv : v.val ∈ F
      · simp only [color, dif_pos hu, dif_pos hv, ne_eq, Sum.inr.injEq]
        exact CF.valid huv
      · simp only [color, dif_pos hu, dif_neg hv, ne_eq, Sum.inr_ne_inl, not_false_eq_true]
    · by_cases hv : v.val ∈ F
      · simp only [color, dif_neg hu, dif_pos hv, ne_eq, Sum.inl_ne_inr, not_false_eq_true]
      · simp only [color, dif_neg hu, dif_neg hv, ne_eq, Sum.inl.injEq]
        exact CG.valid (hag u.val u.2 v.val v.2 hu hv huv)
  let C := SimpleGraph.Coloring.mk color hvalid
  have hh := C.colorable
  simpa only [Fintype.card_sum, Fintype.card_fin] using hh

lemma chiSet_splice {n k : ℕ} (G H : SimpleGraph (Fin n)) (A F : Finset (Fin n))
    (hF : chiSet H F ≤ k)
    (hag : ∀ u ∈ A, ∀ v ∈ A, u ∉ F → v ∉ F → H.Adj u v → G.Adj u v) :
    chiSet H A ≤ chiSet G A + k := by
  have hh := colorable_splice G H A F (chiSet_colorable G A)
    (SimpleGraph.chromaticNumber_le_iff_colorable.mp hF) hag
  have hc := hh.chromaticNumber_le
  change (H.induce (A : Set (Fin n))).chromaticNumber ≤ chiSet G A + k
  simpa only [Nat.cast_add, chiSet_natCast] using hc

end TalagrandConc.Chromatic.Fresh
end

section
noncomputable section
open scoped Classical
namespace TalagrandConc.Chromatic.Fresh

lemma rowGraph_adj_iff {n : ℕ} (x y : Rows n) {u v : Fin n}
    (hu : x u = y u) (hv : x v = y v) :
    (rowGraph x).Adj u v ↔ (rowGraph y).Adj u v := by
  simp only [rowGraph, graphOf, SimpleGraph.fromRel_adj, rowEdges]
  rw [hu, hv]

def mismatchSet {n : ℕ} (x y : Rows n) (A : Finset (Fin n)) : Finset (Fin n) :=
  A.filter (fun j => x j ≠ y j)

lemma chiSet_row_splice {n k : ℕ} (x y : Rows n) (A : Finset (Fin n))
    (hF : chiSet (rowGraph y) (mismatchSet x y A) ≤ k) :
    chiSet (rowGraph y) A ≤ chiSet (rowGraph x) A + k := by
  apply chiSet_splice (rowGraph x) (rowGraph y) A (mismatchSet x y A) hF
  intro u hu v hv huf hvf hadj
  have hue : x u = y u := by
    by_contra h
    exact huf (Finset.mem_filter.mpr ⟨hu, h⟩)
  have hve : x v = y v := by
    by_contra h
    exact hvf (Finset.mem_filter.mpr ⟨hv, h⟩)
  exact (rowGraph_adj_iff x y hue hve).mpr hadj

lemma chiSet_le_localSup {n k : ℕ} (G : SimpleGraph (Fin n)) (s : ℝ)
    (hG : localSup G s ≤ k) (F : Finset (Fin n)) (hF : (F.card : ℝ) ≤ s) :
    chiSet G F ≤ k :=
  (le_iSup_of_le F (le_iSup (fun _ : (F.card : ℝ) ≤ s => chiSet G F) hF)).trans hG

end TalagrandConc.Chromatic.Fresh
end

section
noncomputable section
open scoped Classical
namespace TalagrandConc.Chromatic.Fresh

lemma row_mismatch_lower {n m : ℕ} (hm : m ≤ n) (x : Rows n) (a k : ℕ) (t : ℝ)
    (hwit : ∀ A : Finset (Fin n), A.card = m → ∃ y : Rows n,
      a ≤ chiNat (rowGraph y) m ∧ localSup (rowGraph y) (t * Real.sqrt m) ≤ k ∧
        ((mismatchSet x y A).card : ℝ) ≤ t * Real.sqrt m) :
    a ≤ chiNat (rowGraph x) m + k := by
  have hset (A : Finset (Fin n)) (hA : A.card = m) :
      ((a - k : ℕ) : ℕ∞) ≤ chiSet (rowGraph x) A := by
    obtain ⟨y, ha, hy, hF⟩ := hwit A hA
    have hcolor := chiSet_row_splice x y A
      (chiSet_le_localSup (rowGraph y) _ hy _ hF)
    have hah : (a : ℕ∞) ≤ chiSet (rowGraph y) A :=
      (show (a : ℕ∞) ≤ (chiNat (rowGraph y) m : ℕ∞) by exact_mod_cast ha).trans
        ((chiNat_cast (rowGraph y) hm).le.trans (chiM_le_chiSet (rowGraph y) A hA))
    have hbound := hah.trans hcolor
    rw [← chiSet_natCast (rowGraph x) A, ← Nat.cast_add] at hbound
    have hnat : a ≤ (chiSet (rowGraph x) A).toNat + k := by exact_mod_cast hbound
    rw [← chiSet_natCast (rowGraph x) A]
    exact_mod_cast (Nat.sub_le_iff_le_add.mpr hnat)
  have hlow : ((a - k : ℕ) : ℕ∞) ≤ chiM (rowGraph x) m :=
    le_iInf (fun A => le_iInf (fun hA => hset A hA))
  rw [← chiNat_cast (rowGraph x) hm] at hlow
  have hh : a - k ≤ chiNat (rowGraph x) m := by exact_mod_cast hlow
  exact Nat.sub_le_iff_le_add.mp hh

lemma row_mismatch_lower_int {n m : ℕ} (hm : m ≤ n) (x : Rows n) (a k : ℕ)
    (h : a ≤ chiNat (rowGraph x) m + k) :
    (((a : ℤ) - k : ℤ) : WithTop ℤ) ≤ chiMZ (rowGraph x) m := by
  rw [chiMZ_eq (rowGraph x) hm]
  have hh : (a : ℤ) - k ≤ (chiNat (rowGraph x) m : ℤ) := by omega
  exact_mod_cast hh

end TalagrandConc.Chromatic.Fresh
end

section

noncomputable section
namespace TalagrandConc.Chromatic.Fresh

lemma finite_upper_quantile (F : ℕ → ℝ) (m : ℕ) (δ : ℝ)
    (hzero : δ ≤ F 0) (hend : F (m + 1) < δ) :
    ∃ a ≤ m, δ ≤ F a ∧ F (a + 1) < δ := by
  classical
  let a := Nat.findGreatest (fun i => δ ≤ F i) m
  have ha : a ≤ m := Nat.findGreatest_le m
  have hFa : δ ≤ F a := Nat.findGreatest_spec (P := fun i => δ ≤ F i) (Nat.zero_le m) hzero
  refine ⟨a, ha, hFa, ?_⟩
  by_cases he : a = m
  · simpa [he] using hend
  · have hi : a + 1 ≤ m := by omega
    have hh : ¬δ ≤ F (a + 1) := Nat.findGreatest_is_greatest (P := fun i => δ ≤ F i) (by
      change a < a + 1
      omega) hi
    exact lt_of_not_ge hh

lemma good_integer_quantile {Ω : Type*} (mass : Set Ω → ℝ)
    (hempty : mass ∅ = 0) (G : Set Ω) (q : Ω → ℕ) (m : ℕ)
    (hq : ∀ x, q x ≤ m) (δ : ℝ) (hδ : 0 < δ) (hG : δ ≤ mass G) :
    ∃ a ≤ m,
      δ ≤ mass {x | x ∈ G ∧ a ≤ q x} ∧
      mass {x | x ∈ G ∧ a < q x} < δ := by
  let F : ℕ → ℝ := fun i => mass {x | x ∈ G ∧ i ≤ q x}
  have hzero : δ ≤ F 0 := by simpa [F] using hG
  have hend : F (m + 1) < δ := by
    have hs : {x | x ∈ G ∧ m + 1 ≤ q x} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hh
      have hb := hq x
      omega
    change mass {x | x ∈ G ∧ m + 1 ≤ q x} < δ
    rw [hs, hempty]
    exact hδ
  obtain ⟨a, ha, hFa, hnext⟩ := finite_upper_quantile F m δ hzero hend
  refine ⟨a, ha, hFa, ?_⟩
  have hs : {x | x ∈ G ∧ a < q x} = {x | x ∈ G ∧ a + 1 ≤ q x} := by
    ext x
    change (x ∈ G ∧ a < q x) ↔ (x ∈ G ∧ a + 1 ≤ q x)
    constructor <;> rintro ⟨hg, hh⟩ <;> exact ⟨hg, by omega⟩
  rw [hs]
  exact hnext

end TalagrandConc.Chromatic.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace TalagrandConc.Chromatic.Fresh

lemma productMass_univ {α : Type*} [Fintype α] {p : α → ℝ}
    (hs : ∑ a, p a = 1) (n : ℕ) : productMass p n Set.univ = 1 := by
  classical
  simpa [productMass, productMean, finiteMean] using productWeight_sum hs n

lemma productMass_add_compl {α : Type*} [Fintype α] {p : α → ℝ}
    (hs : ∑ a, p a = 1) (n : ℕ) (A : Set (Fin n → α)) :
    productMass p n A + productMass p n Aᶜ = 1 := by
  classical
  have he : productMass p n A + productMass p n Aᶜ = ∑ x, productWeight p n x := by
    unfold productMass productMean finiteMean
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ A <;> simp [hx]
  rw [he, productWeight_sum hs n]

lemma productMass_compl {α : Type*} [Fintype α] {p : α → ℝ}
    (hs : ∑ a, p a = 1) (n : ℕ) (A : Set (Fin n → α)) :
    productMass p n Aᶜ = 1 - productMass p n A := by
  have h := productMass_add_compl hs n A
  linarith

lemma productMass_union_le {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (n : ℕ) (A B : Set (Fin n → α)) :
    productMass p n (A ∪ B) ≤ productMass p n A + productMass p n B := by
  classical
  unfold productMass productMean finiteMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hw := productWeight_nonneg hp n x
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb]
  linarith

lemma productMass_good_quantile {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (n m : ℕ) (q : (Fin n → α) → ℕ)
    (hq : ∀ x, q x ≤ m) (G : Set (Fin n → α)) (δ : ℝ)
    (hδ : 0 < δ) (hG : δ ≤ productMass p n G) :
    ∃ a ≤ m, δ ≤ productMass p n (G ∩ {x | a ≤ q x}) ∧
      productMass p n {x | a < q x} ≤ δ + productMass p n Gᶜ := by
  obtain ⟨a, ha, hlow, hhigh⟩ := good_integer_quantile
    (productMass p n) (productMass_empty p n) G q m hq δ hδ hG
  refine ⟨a, ha, hlow, ?_⟩
  have hsub : {x | a < q x} ⊆ {x | x ∈ G ∧ a < q x} ∪ Gᶜ := by
    intro x hx
    by_cases hg : x ∈ G
    · exact Or.inl ⟨hg, hx⟩
    · exact Or.inr hg
  calc
    productMass p n {x | a < q x} ≤
        productMass p n ({x | x ∈ G ∧ a < q x} ∪ Gᶜ) := productMass_mono hp hsub
    _ ≤ productMass p n {x | x ∈ G ∧ a < q x} + productMass p n Gᶜ :=
      productMass_union_le hp n _ _
    _ ≤ δ + productMass p n Gᶜ := add_le_add hhigh.le le_rfl

end TalagrandConc.Chromatic.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace TalagrandConc.Chromatic.Fresh

lemma productMass_interval_lower {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (n : ℕ) (χ : (Fin n → α) → ℕ) (a k : ℕ) (δ q : ℝ)
    (hlo : productMass p n {x | χ x + k < a} ≤ δ)
    (hhi : productMass p n {x | a < χ x} ≤ δ + q) :
    1 - 2 * δ - q ≤ productMass p n {x | a ≤ χ x + k ∧ χ x ≤ a} := by
  let I : Set (Fin n → α) := {x | a ≤ χ x + k ∧ χ x ≤ a}
  have hc : Iᶜ = {x | χ x + k < a} ∪ {x | a < χ x} := by
    ext x
    change (¬(a ≤ χ x + k ∧ χ x ≤ a)) ↔ (χ x + k < a ∨ a < χ x)
    omega
  have hu := productMass_union_le hp n {x | χ x + k < a} {x | a < χ x}
  have hb : productMass p n Iᶜ ≤ 2 * δ + q := by
    rw [hc]
    linarith
  rw [productMass_compl hs n I] at hb
  change 1 - 2 * δ - q ≤ productMass p n I
  linarith

lemma low_good_mass_trivial {α : Type*} [Fintype α] {p : α → ℝ}
    (hs : ∑ x, p x = 1) (n : ℕ) (G : Set (Fin n → α)) (δ : ℝ)
    (hδ : 0 < δ) (hG : productMass p n G < δ) :
    1 - 2 * δ - productMass p n Gᶜ ≤ 0 := by
  rw [productMass_compl hs n G]
  linarith

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators
open MeasureTheory

namespace TalagrandConc.Chromatic.Fresh

noncomputable def coinWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

lemma coinWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ coinWeight p b := by cases b <;> simp [coinWeight] <;> linarith

lemma coinWeight_sum (p : ℝ) : ∑ b : Bool, coinWeight p b = 1 := by
  simp [coinWeight]

lemma coin_probability {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (coin p) := by
  constructor
  simp only [coin, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _)]
  change (p.toNNReal : ENNReal)*1 + ((1-p).toNNReal : ENNReal)*1 = 1
  simp only [mul_one]
  rw [← ENNReal.coe_add]
  have h : p.toNNReal + (1-p).toNNReal = 1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hp0,
      Real.coe_toNNReal _ (sub_nonneg.mpr hp1), NNReal.coe_one]
    ring
  rw [h]
  rfl

lemma coin_singleton {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (b : Bool) :
    coin p {b} = ENNReal.ofReal (coinWeight p b) := by
  cases b <;> simp [coin, coinWeight, ENNReal.ofReal]

noncomputable def rowWeight (n : ℕ) (p : ℝ) (x : Fin n → Bool) : ℝ :=
  productWeight (coinWeight p) n x

lemma rowWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (x : Fin n → Bool) :
    0 ≤ rowWeight n p x := productWeight_nonneg (coinWeight_nonneg hp0 hp1) n x

lemma rowWeight_sum (n : ℕ) (p : ℝ) : ∑ x, rowWeight n p x = 1 :=
  productWeight_sum (coinWeight_sum p) n

noncomputable def rowLaw (n : ℕ) (p : ℝ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ : Fin n => coin p)

noncomputable def rowsLaw (n : ℕ) (p : ℝ) : Measure (Rows n) :=
  Measure.pi (fun _ : Fin n => rowLaw n p)

lemma rowLaw_probability {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    IsProbabilityMeasure (rowLaw n p) := by
  let := coin_probability hp0 hp1
  unfold rowLaw
  infer_instance

lemma rowsLaw_probability {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    IsProbabilityMeasure (rowsLaw n p) := by
  let := rowLaw_probability hp0 hp1 n
  unfold rowsLaw
  infer_instance

lemma rowLaw_singleton {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (x : Fin n → Bool) :
    rowLaw n p {x} = ENNReal.ofReal (rowWeight n p x) := by
  let := coin_probability hp0 hp1
  simp only [rowLaw, Measure.pi_singleton, coin_singleton hp0 hp1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => coinWeight_nonneg hp0 hp1 (x i))]
  rfl

lemma rowsLaw_singleton {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (x : Rows n) :
    rowsLaw n p {x} = ENNReal.ofReal (productWeight (rowWeight n p) n x) := by
  let := rowLaw_probability hp0 hp1 n
  simp only [rowsLaw, Measure.pi_singleton, rowLaw_singleton hp0 hp1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => rowWeight_nonneg hp0 hp1 n (x i))]
  rfl

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators Classical

namespace TalagrandConc.Chromatic.Fresh

lemma exponential_tail_budget {t M : ℝ} (hM : Real.exp (-t^2/8) ≤ M) :
    Real.exp (-t^2/4) / M ≤ Real.exp (-t^2/8) := by
  have hd := Real.exp_pos (-t^2/8)
  have hMp : 0 < M := hd.trans_le hM
  apply (div_le_iff₀ hMp).mpr
  have he : Real.exp (-t^2/4) = Real.exp (-t^2/8)*Real.exp (-t^2/8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hM hd.le

lemma finite_chromatic_interval (n m k : ℕ) (p t : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 < t) (hm : m ≤ n) :
    ∃ a : ℕ,
      1 - 2*Real.exp (-t^2/8) -
          productMass (rowWeight n p) n {x | (k : ℕ∞) < localSup (rowGraph x) (t*Real.sqrt m)} ≤
        productMass (rowWeight n p) n
          {x | a ≤ chiNat (rowGraph x) m + k ∧ chiNat (rowGraph x) m ≤ a} := by
  classical
  let G : Set (Rows n) := {x | localSup (rowGraph x) (t*Real.sqrt m) ≤ k}
  let q : Rows n → ℕ := fun x => chiNat (rowGraph x) m
  let δ := Real.exp (-t^2/8)
  have hδ : 0 < δ := Real.exp_pos _
  have hp := rowWeight_nonneg hp0 hp1 n
  have hs := rowWeight_sum n p
  have hGc : Gᶜ = {x | (k : ℕ∞) < localSup (rowGraph x) (t*Real.sqrt m)} := by
    ext x
    simp [G,not_le]
  by_cases hG : δ ≤ productMass (rowWeight n p) n G
  · obtain ⟨a,_,hA,hhigh⟩ := productMass_good_quantile hp n m q
      (fun x => chiNat_le (rowGraph x) hm) G δ hδ hG
    let A := G ∩ {x | a ≤ q x}
    have hAp : 0 < productMass (rowWeight n p) n A := hδ.trans_le hA
    have hAn : A.Nonempty := productMass_pos_nonempty hAp
    have hsub : {x | q x+k<a} ⊆ {x | t^2 ≤ convexDistanceSq A x} := by
      intro x hx
      by_contra hd
      have hlow := row_mismatch_lower hm x a k t (by
        intro H hH
        obtain ⟨y,hy,hw⟩ := distance_subset_witness hAn x ht.le (not_le.mp hd).le H hH
        exact ⟨y,hy.2,hy.1,hw⟩)
      change q x+k<a at hx
      change a ≤ q x+k at hlow
      omega
    have hlow : productMass (rowWeight n p) n {x | q x+k<a} ≤ δ := by
      calc
        _ ≤ productMass (rowWeight n p) n {x | t^2 ≤ convexDistanceSq A x} :=
          productMass_mono hp hsub
        _ ≤ Real.exp (-t^2/4)/productMass (rowWeight n p) n A :=
          finite_convex_distance_tail hp hs n A hAp (t^2)
        _ ≤ δ := exponential_tail_budget hA
    refine ⟨a,?_⟩
    have hh := productMass_interval_lower hp hs n q a k δ
      (productMass (rowWeight n p) n Gᶜ) hlow hhigh
    simpa only [hGc] using hh
  · refine ⟨0,?_⟩
    have htr := low_good_mass_trivial hs n G δ hδ (not_le.mp hG)
    have hn := productMass_nonneg hp n
      {x | 0 ≤ chiNat (rowGraph x) m+k ∧ chiNat (rowGraph x) m ≤ 0}
    rw [hGc] at htr
    exact htr.trans hn

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators Classical
open MeasureTheory

namespace TalagrandConc.Chromatic.Fresh

lemma real_finite_atoms {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Set Ω) : μ.real A = ∑ x, if x ∈ A then (μ {x}).toReal else 0 := by
  classical
  calc
    μ.real A = ∑ x ∈ A.toFinset, μ.real {x} := by
      rw [sum_measureReal_singleton, Set.coe_toFinset]
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp

lemma rowsLaw_real {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (A : Set (Rows n)) :
    (rowsLaw n p).real A = productMass (rowWeight n p) n A := by
  classical
  let := rowsLaw_probability hp0 hp1 n
  rw [real_finite_atoms]
  simp only [rowsLaw_singleton hp0 hp1, ENNReal.toReal_ofReal
    (productWeight_nonneg (rowWeight_nonneg hp0 hp1 n) n _)]
  unfold productMass productMean finiteMean
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ A <;> simp [hx]

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators

namespace TalagrandConc.Chromatic.Fresh

lemma triangle_prod {M : Type*} [CommMonoid M] (n : ℕ) (f : EdgeSlot n → M) :
    (∏ j : Fin n, ∏ i : Fin n, if h : i < j then f ⟨(i,j),h⟩ else 1) =
      ∏ e : EdgeSlot n, f e := by
  classical
  rw [Finset.prod_comm]
  let g : Fin n × Fin n → M := fun e => if h : e.1 < e.2 then f ⟨e,h⟩ else 1
  change (∏ i, ∏ j, g (i,j)) = _
  rw [← Fintype.prod_prod_type g]
  have he : (∏ e, g e) = ∏ e ∈ (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2)), g e := by
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro e _ he
    have h : ¬ e.1 < e.2 := by simpa using he
    simp [g,h]
  rw [he]
  rw [Finset.prod_subtype (p := fun e : Fin n × Fin n => e.1 < e.2) _ (by simp)]
  apply Finset.prod_congr rfl
  intro e _
  simp [g,e.property]

end TalagrandConc.Chromatic.Fresh
end

section

open scoped BigOperators
open MeasureTheory

namespace TalagrandConc.Chromatic.Fresh

noncomputable def edgeRectangle {n : ℕ} (x : EdgeSlot n → Bool) (j i : Fin n) : Set Bool :=
  if h : i < j then {x ⟨(i,j),h⟩} else Set.univ

lemma rowEdges_preimage_singleton {n : ℕ} (x : EdgeSlot n → Bool) :
    rowEdges ⁻¹' {x} = Set.univ.pi (fun j => Set.univ.pi (edgeRectangle x j)) := by
  classical
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro h j i
    by_cases hij : i < j
    · have he := congrFun h (⟨(i,j),hij⟩ : EdgeSlot n)
      simpa [edgeRectangle,hij,rowEdges] using he
    · simp [edgeRectangle,hij]
  · intro h
    funext e
    have he := h e.val.2 e.val.1
    simpa [edgeRectangle,e.property,rowEdges] using he

lemma rowsLaw_map_edges {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (rowsLaw n p).map rowEdges = gnp n p := by
  classical
  let := coin_probability hp0 hp1
  let := rowLaw_probability hp0 hp1 n
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable rowEdges) (measurableSet_singleton x),
    rowEdges_preimage_singleton]
  simp only [rowsLaw, Measure.pi_pi, rowLaw, gnp, Measure.pi_singleton]
  rw [← triangle_prod n (fun e => coin p {x e})]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hij : i < j
  · simp only [edgeRectangle, dif_pos hij]
  · simp only [edgeRectangle, dif_neg hij, measure_univ]

lemma rowsLaw_real_preimage {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (A : Set (EdgeSlot n → Bool)) :
    (rowsLaw n p).real (rowEdges ⁻¹' A) = (gnp n p).real A := by
  rw [← rowsLaw_map_edges hp0 hp1 n]
  rw [measureReal_def, measureReal_def,
    Measure.map_apply (measurable_of_countable rowEdges) (Set.toFinite A).measurableSet]

end TalagrandConc.Chromatic.Fresh
end

section

open MeasureTheory
open scoped Classical

namespace TalagrandConc.Chromatic.Fresh

lemma mass_rowEdges {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (A : Set (EdgeSlot n → Bool)) :
    productMass (rowWeight n p) n (rowEdges ⁻¹' A) = (gnp n p).real A := by
  rw [← rowsLaw_real hp0 hp1 n, rowsLaw_real_preimage hp0 hp1 n]

lemma interval_preimage {n m : ℕ} (hm : m ≤ n) (a k : ℕ) :
    {x : Rows n | a ≤ chiNat (rowGraph x) m+k ∧ chiNat (rowGraph x) m ≤ a} =
      rowEdges ⁻¹' {x | (((a : ℤ)-k : ℤ) : WithTop ℤ) ≤ chiMZ (graphOf x) m ∧
        chiMZ (graphOf x) m ≤ ((a : ℤ) : WithTop ℤ)} := by
  ext x
  change (a ≤ chiNat (rowGraph x) m+k ∧ chiNat (rowGraph x) m ≤ a) ↔ _
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, rowGraph, chiMZ_eq _ hm,
    WithTop.coe_le_coe]
  omega

lemma native_chromatic_interval {n m k : ℕ} {p t : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : m ≤ n) (a : ℕ)
    (h : 1 - 2*Real.exp (-t^2/8) -
      productMass (rowWeight n p) n {x | (k : ℕ∞) < localSup (rowGraph x) (t*Real.sqrt m)} ≤
      productMass (rowWeight n p) n
        {x | a ≤ chiNat (rowGraph x) m+k ∧ chiNat (rowGraph x) m ≤ a}) :
    1 - 2*Real.exp (-t^2/8) -
      (gnp n p).real {x | (k : ℕ∞) < localSup (graphOf x) (t*Real.sqrt m)} ≤
      (gnp n p).real {x | (((a : ℤ)-k : ℤ) : WithTop ℤ) ≤ chiMZ (graphOf x) m ∧
        chiMZ (graphOf x) m ≤ ((a : ℤ) : WithTop ℤ)} := by
  rw [interval_preimage hm a k, mass_rowEdges hp0 hp1 n] at h
  have he : {x : Rows n | (k : ℕ∞) < localSup (rowGraph x) (t*Real.sqrt m)} =
      rowEdges ⁻¹' {x | (k : ℕ∞) < localSup (graphOf x) (t*Real.sqrt m)} := rfl
  rw [he,mass_rowEdges hp0 hp1 n] at h
  exact h

end TalagrandConc.Chromatic.Fresh
end

section

open MeasureTheory
open scoped Classical

namespace TalagrandConc.Chromatic

theorem native_theorem_9_1 (n m k : ℕ) (p t : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (ht : 0 < t)
    (hm : m ≤ n) :
    ∃ a : ℤ,
      1 - 2 * Real.exp (-t ^ 2 / 8)
          - (gnp n p).real {x | (k : ℕ∞) < localSup (graphOf x) (t * Real.sqrt m)}
        ≤ (gnp n p).real {x | (((a - k : ℤ)) : WithTop ℤ) ≤ chiMZ (graphOf x) m ∧
            chiMZ (graphOf x) m ≤ (a : WithTop ℤ)} := by
  obtain ⟨a,ha⟩ := Fresh.finite_chromatic_interval n m k p t hp0.le hp1.le ht hm
  exact ⟨(a : ℤ),Fresh.native_chromatic_interval hp0.le hp1.le hm a ha⟩

end TalagrandConc.Chromatic
end

open TalagrandConc.Chromatic

theorem solution (n m k : ℕ) (p t : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (ht : 0 < t)
    (hm : m ≤ n) :
    ∃ a : ℤ,
      1 - 2 * Real.exp (-t ^ 2 / 8)
          - (gnp n p).real {x | (k : ℕ∞) < localSup (graphOf x) (t * Real.sqrt m)}
        ≤ (gnp n p).real {x | (((a - k : ℤ)) : WithTop ℤ) ≤ chiMZ (graphOf x) m ∧
            chiMZ (graphOf x) m ≤ (a : WithTop ℤ)} := by
  exact native_theorem_9_1 n m k p t hp0 hp1 ht hm
