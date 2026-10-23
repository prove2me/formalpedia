-- Prove2me | solution 1 for RiskFunctionals.NestedAVaR.composition_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:06:02.656612+00:00
-- url     : https://prove2.me/submissions/12d5ef67-22d3-4a8e-9c38-646bf36fd71e

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions

open RiskFunctionals.NestedAVaR

open MeasureTheory

section g79t
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} {ℱ : Filtration ℕ mΩ}
  {p : ENNReal} {T : ℕ} {A : ℕ → (Ω → ℝ) → Ω → ℝ}

theorem g79t_Lmono {s t : ℕ} (hst : s ≤ t) {X : Ω → ℝ} (h : IsLp (ℱ s) P p X) :
    IsLp (ℱ t) P p X := ⟨h.1.mono (ℱ.mono hst) le_rfl, h.2⟩

theorem g79t_Ladd {s : ℕ} {X W : Ω → ℝ} (hX : IsLp (ℱ s) P p X) (hW : IsLp (ℱ s) P p W) :
    IsLp (ℱ s) P p (X + W) := ⟨hX.1.add hW.1, hX.2.add hW.2⟩

theorem g79t_Lconst [IsFiniteMeasure P] (s : ℕ) (c : ℝ) :
    IsLp (ℱ s) P p (fun _ => c) := ⟨measurable_const, memLp_const c⟩

theorem g79t_Lsmul {s : ℕ} (l : ℝ) {X : Ω → ℝ} (hX : IsLp (ℱ s) P p X) :
    IsLp (ℱ s) P p (l • X) := ⟨hX.1.const_smul l, hX.2.const_smul l⟩

theorem g79t_Lsum {s : ℕ} (I : Finset ℕ) {Y : ℕ → Ω → ℝ} (h : ∀ t ∈ I, IsLp (ℱ s) P p (Y t)) :
    IsLp (ℱ s) P p (fun ω => ∑ t ∈ I, Y t ω) :=
  ⟨Finset.measurable_sum I (fun t ht => (h t ht).1), memLp_finset_sum I (fun t ht => (h t ht).2)⟩

theorem g79t_comp_L (hA : IsConditionalAcceptabilityFamily ℱ P p T A) :
    ∀ t, t ≤ T → ∀ X, IsLp (ℱ T) P p X → IsLp (ℱ T) P p (composition A t X) := by
  intro t
  induction t with
  | zero => intro _ X hX; exact hX
  | succ t ih =>
    intro ht X hX
    exact ih (by omega) (A t X) (g79t_Lmono (t := T) (by omega) (hA.mapsTo t (by omega) X hX))

theorem g79t_comp_mono (hA : IsConditionalAcceptabilityFamily ℱ P p T A) :
    ∀ t, t ≤ T → ∀ X X', IsLp (ℱ T) P p X → IsLp (ℱ T) P p X' → X ≤ᵐ[P] X' →
      composition A t X ≤ᵐ[P] composition A t X' := by
  intro t
  induction t with
  | zero => intro _ X X' _ _ h; exact h
  | succ t ih =>
    intro ht X X' hX hX' h
    exact ih (by omega) (A t X) (A t X')
      (g79t_Lmono (t := T) (by omega) (hA.mapsTo t (by omega) X hX))
      (g79t_Lmono (t := T) (by omega) (hA.mapsTo t (by omega) X' hX'))
      (hA.monotone t (by omega) X X' hX hX' h)

theorem g79t_comp_congr (hA : IsConditionalAcceptabilityFamily ℱ P p T A) {t : ℕ} (ht : t ≤ T)
    {X X' : Ω → ℝ} (hX : IsLp (ℱ T) P p X) (hX' : IsLp (ℱ T) P p X') (h : X =ᵐ[P] X') :
    composition A t X =ᵐ[P] composition A t X' :=
  (g79t_comp_mono hA t ht X X' hX hX' h.le).antisymm
    (g79t_comp_mono hA t ht X' X hX' hX h.symm.le)

theorem g79t_comp_trans [IsFiniteMeasure P] (hA : IsConditionalAcceptabilityFamily ℱ P p T A) :
    ∀ t, t ≤ T → ∀ X, IsLp (ℱ T) P p X → ∀ c : ℝ,
      composition A t (X + fun _ => c) =ᵐ[P] composition A t X + fun _ => c := by
  intro t
  induction t with
  | zero => intro _ X _ c; rfl
  | succ t ih =>
    intro ht X hX c
    show composition A t (A t (X + fun _ => c)) =ᵐ[P] composition A t (A t X) + fun _ => c
    have hAX := g79t_Lmono (t := T) (by omega) (hA.mapsTo t (by omega) X hX)
    have h1 := hA.translation t (by omega) X (fun _ => c) hX (g79t_Lconst t c)
    refine (g79t_comp_congr hA (by omega)
      (g79t_Lmono (t := T) (by omega) (hA.mapsTo t (by omega) _ (g79t_Ladd hX (g79t_Lconst T c))))
      (g79t_Ladd hAX (g79t_Lconst T c)) h1).trans ?_
    exact ih (by omega) (A t X) hAX c

theorem g79t_comp_conc (hA : IsConditionalAcceptabilityFamily ℱ P p T A) :
    ∀ t, t ≤ T → ∀ X X', IsLp (ℱ T) P p X → IsLp (ℱ T) P p X' → ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
      (fun ω => l * composition A t X ω + (1 - l) * composition A t X' ω) ≤ᵐ[P]
        composition A t (l • X + (1 - l) • X') := by
  intro t
  induction t with
  | zero =>
    intro _ X X' _ _ l _ _
    exact Filter.Eventually.of_forall fun ω => by simp [composition]
  | succ t ih =>
    intro ht X X' hX hX' l hl0 hl1
    show (fun ω => l * composition A t (A t X) ω + (1 - l) * composition A t (A t X') ω) ≤ᵐ[P]
      composition A t (A t (l • X + (1 - l) • X'))
    have hAX := g79t_Lmono (t := T) (by omega) (hA.mapsTo t (by omega) X hX)
    have hAX' := g79t_Lmono (t := T) (by omega) (hA.mapsTo t (by omega) X' hX')
    have hmix : IsLp (ℱ T) P p (l • X + (1 - l) • X') :=
      g79t_Ladd (g79t_Lsmul l hX) (g79t_Lsmul (1 - l) hX')
    refine (ih (by omega) _ _ hAX hAX' l hl0 hl1).trans ?_
    refine g79t_comp_mono hA t (by omega) _ _
      (g79t_Ladd (g79t_Lsmul l hAX) (g79t_Lsmul (1 - l) hAX'))
      (g79t_Lmono (t := T) (by omega) (hA.mapsTo t (by omega) _ hmix)) ?_
    have := hA.concave t (by omega) X X' hX hX' l hl0 hl1
    refine Filter.EventuallyLE.trans ?_ this
    exact Filter.Eventually.of_forall fun ω => by simp

theorem g79t_comp_hom (hA : IsConditionalAcceptabilityFamily ℱ P p T A)
    (hH : IsPositivelyHomogeneousFamily ℱ P p T A) :
    ∀ t, t ≤ T → ∀ X, IsLp (ℱ T) P p X → ∀ l : ℝ, 0 < l →
      composition A t (l • X) =ᵐ[P] l • composition A t X := by
  intro t
  induction t with
  | zero => intro _ X _ l _; rfl
  | succ t ih =>
    intro ht X hX l hl
    show composition A t (A t (l • X)) =ᵐ[P] l • composition A t (A t X)
    have hAX := g79t_Lmono (t := T) (by omega) (hA.mapsTo t (by omega) X hX)
    refine (g79t_comp_congr hA (by omega)
      (g79t_Lmono (t := T) (by omega) (hA.mapsTo t (by omega) _ (g79t_Lsmul l hX)))
      (g79t_Lsmul l hAX) (hH t (by omega) X hX l hl)).trans ?_
    exact ih (by omega) (A t X) hAX l hl

theorem g79t_nested (hA : IsConditionalAcceptabilityFamily ℱ P p T A) (Y : ℕ → Ω → ℝ)
    (hY : ∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) :
    ∀ n, n ≤ T → ∀ b, IsLp (ℱ n) P p b →
      (List.range n).foldr (fun s acc => A s (Y (s + 1) + acc)) b =ᵐ[P]
        composition A n (b + fun ω => ∑ t ∈ Finset.Icc 1 n, Y t ω) := by
  intro n
  induction n with
  | zero => intro _ b _; exact Filter.Eventually.of_forall fun ω => by simp [composition]
  | succ n ih =>
    intro hn b hb
    rw [List.range_succ, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    have hYn : IsLp (ℱ (n + 1)) P p (Y (n + 1)) := hY (n + 1) (by simp; omega)
    have hX : IsLp (ℱ T) P p (Y (n + 1) + b) :=
      g79t_Ladd (g79t_Lmono hn hYn) (g79t_Lmono (t := T) (by omega) hb)
    have hb' := hA.mapsTo n (by omega) _ hX
    have hS : IsLp (ℱ n) P p (fun ω => ∑ t ∈ Finset.Icc 1 n, Y t ω) :=
      g79t_Lsum _ fun t ht => g79t_Lmono (by simp at ht; omega)
        (hY t (by simp at ht ⊢; omega))
    refine (ih (by omega) _ hb').trans ?_
    have h1 := hA.translation n (by omega) _ _ hX hS
    have h2 := g79t_comp_congr hA (p := p) (t := n) (by omega)
      (g79t_Lmono (t := T) (by omega) (hA.mapsTo n (by omega) _ (g79t_Ladd hX (g79t_Lmono (t := T) (by omega) hS))))
      (g79t_Ladd (g79t_Lmono (t := T) (by omega) hb') (g79t_Lmono (t := T) (by omega) hS)) h1
    refine h2.symm.trans (Filter.Eventually.of_forall fun ω => ?_)
    show composition A n (A n (Y (n + 1) + b + fun ω => ∑ t ∈ Finset.Icc 1 n, Y t ω)) ω =
      composition A n (A n (b + fun ω => ∑ t ∈ Finset.Icc 1 (n + 1), Y t ω)) ω
    have e : (Y (n + 1) + b + fun ω => ∑ t ∈ Finset.Icc 1 n, Y t ω) =
        (b + fun ω => ∑ t ∈ Finset.Icc 1 (n + 1), Y t ω) := by
      funext ω'
      simp only [Pi.add_apply]
      rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
      ring
    rw [e]

end g79t

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (p : ENNReal) (hp₁ : 1 ≤ p) (hp_top : p ≠ ⊤)
    (A : ℕ → (Ω → ℝ) → Ω → ℝ) (hA : IsConditionalAcceptabilityFamily ℱ P p T A) :
    -- (MA1′) weak translation-equivariance (3.16)
    (∀ Y : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
      ∀ t ∈ Finset.Icc 1 T, ∀ c : ℝ,
        nestedValue P A (Function.update Y t (fun ω => Y t ω + c)) T
          = c + nestedValue P A Y T) ∧
    -- (MA2) concavity
    (∀ Y Y' : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
      (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y' t)) →
      ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
        l * nestedValue P A Y T + (1 - l) * nestedValue P A Y' T
          ≤ nestedValue P A (l • Y + (1 - l) • Y') T) ∧
    -- (MA3) monotonicity
    (∀ Y Y' : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
      (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y' t)) →
      (∀ t ∈ Finset.Icc 1 T, Y t ≤ᵐ[P] Y' t) →
        nestedValue P A Y T ≤ nestedValue P A Y' T) ∧
    -- every 𝒜⁽ᵗ⁾ is a (single-period) acceptability functional on 𝒴_T: (A1)–(A3)
    (∀ t ∈ Finset.Icc 1 T,
      (∀ X : Ω → ℝ, IsLp (ℱ T) P p X → ∀ c : ℝ,
        compositionValue P A t (fun ω => X ω + c) = compositionValue P A t X + c) ∧
      (∀ X X' : Ω → ℝ, IsLp (ℱ T) P p X → IsLp (ℱ T) P p X' →
        ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
          l * compositionValue P A t X + (1 - l) * compositionValue P A t X'
            ≤ compositionValue P A t (l • X + (1 - l) • X')) ∧
      (∀ X X' : Ω → ℝ, IsLp (ℱ T) P p X → IsLp (ℱ T) P p X' → X ≤ᵐ[P] X' →
        compositionValue P A t X ≤ compositionValue P A t X')) ∧
    -- (3.47)
    (∀ Y : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
      nestedValue P A Y T
        = compositionValue P A T (fun ω => ∑ t ∈ Finset.Icc 1 T, Y t ω)) ∧
    -- positive homogeneity is inherited from the 𝒜_t
    (IsPositivelyHomogeneousFamily ℱ P p T A →
      (∀ Y : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
        ∀ l : ℝ, 0 < l → nestedValue P A (l • Y) T = l * nestedValue P A Y T) ∧
      (∀ t ∈ Finset.Icc 1 T, ∀ X : Ω → ℝ, IsLp (ℱ T) P p X →
        ∀ l : ℝ, 0 < l → compositionValue P A t (l • X) = l * compositionValue P A t X)) := by
  have hint : ∀ X : Ω → ℝ, IsLp (ℱ T) P p X → Integrable X P := fun X hX =>
    hX.2.integrable hp₁
  -- (3.47)
  have h347 : ∀ Y : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
      nestedValue P A Y T
        = compositionValue P A T (fun ω => ∑ t ∈ Finset.Icc 1 T, Y t ω) := by
    intro Y hY
    unfold nestedValue nestedFunctional compositionValue
    refine integral_congr_ae ((g79t_nested hA Y hY T le_rfl 0 ⟨measurable_const, MemLp.zero⟩).trans
      (Filter.Eventually.of_forall fun ω => ?_))
    simp only [zero_add]
  have hSL : ∀ Y : ℕ → Ω → ℝ, (∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p (Y t)) →
      IsLp (ℱ T) P p (fun ω => ∑ t ∈ Finset.Icc 1 T, Y t ω) := fun Y hY =>
    g79t_Lsum _ fun t ht => g79t_Lmono (by simp at ht; omega) (hY t ht)
  -- composition values
  have hA1 : ∀ t, t ≤ T → ∀ X : Ω → ℝ, IsLp (ℱ T) P p X → ∀ c : ℝ,
      compositionValue P A t (fun ω => X ω + c) = compositionValue P A t X + c := by
    intro t ht X hX c
    unfold compositionValue
    show ∫ ω, composition A t (X + fun _ => c) ω ∂P = _
    rw [integral_congr_ae (g79t_comp_trans hA t ht X hX c)]
    rw [integral_add' (hint _ (g79t_comp_L hA t ht X hX)) (integrable_const c)]
    simp
  have hA2 : ∀ t, t ≤ T → ∀ X X' : Ω → ℝ, IsLp (ℱ T) P p X → IsLp (ℱ T) P p X' →
      ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
        l * compositionValue P A t X + (1 - l) * compositionValue P A t X'
          ≤ compositionValue P A t (l • X + (1 - l) • X') := by
    intro t ht X X' hX hX' l hl0 hl1
    unfold compositionValue
    have i1 := hint _ (g79t_comp_L hA t ht X hX)
    have i2 := hint _ (g79t_comp_L hA t ht X' hX')
    have i3 := hint _ (g79t_comp_L hA t ht _ (g79t_Ladd (g79t_Lsmul l hX) (g79t_Lsmul (1 - l) hX')))
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul l) (i2.const_mul _)]
    exact integral_mono_ae ((i1.const_mul l).add (i2.const_mul _)) i3
      (g79t_comp_conc hA t ht X X' hX hX' l hl0 hl1)
  have hA3 : ∀ t, t ≤ T → ∀ X X' : Ω → ℝ, IsLp (ℱ T) P p X → IsLp (ℱ T) P p X' → X ≤ᵐ[P] X' →
      compositionValue P A t X ≤ compositionValue P A t X' := by
    intro t ht X X' hX hX' h
    exact integral_mono_ae (hint _ (g79t_comp_L hA t ht X hX)) (hint _ (g79t_comp_L hA t ht X' hX'))
      (g79t_comp_mono hA t ht X X' hX hX' h)
  refine ⟨?_, ?_, ?_, ?_, h347, ?_⟩
  · intro Y hY t ht c
    have hY' : ∀ s ∈ Finset.Icc 1 T,
        IsLp (ℱ s) P p (Function.update Y t (fun ω => Y t ω + c) s) := by
      intro s hs
      by_cases h : s = t
      · subst h; simp only [Function.update_self]
        exact g79t_Ladd (hY s hs) (g79t_Lconst s c)
      · rw [Function.update_of_ne h]; exact hY s hs
    rw [h347 _ hY', h347 _ hY]
    have hsum : (fun ω => ∑ s ∈ Finset.Icc 1 T, Function.update Y t (fun ω => Y t ω + c) s ω)
        = fun ω => (∑ s ∈ Finset.Icc 1 T, Y s ω) + c := by
      funext ω
      have : ∀ s, Function.update Y t (fun ω => Y t ω + c) s ω = Y s ω + if s = t then c else 0 := by
        intro s
        by_cases h : s = t
        · subst h; simp
        · rw [Function.update_of_ne h]; simp [h]
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos ht]
    rw [hsum, hA1 T le_rfl _ (hSL Y hY) c]
    ring
  · intro Y Y' hY hY' l hl0 hl1
    have hmix : ∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p ((l • Y + (1 - l) • Y') t) := fun t ht =>
      g79t_Ladd (g79t_Lsmul l (hY t ht)) (g79t_Lsmul (1 - l) (hY' t ht))
    rw [h347 _ hY, h347 _ hY', h347 _ hmix]
    have : (fun ω => ∑ t ∈ Finset.Icc 1 T, (l • Y + (1 - l) • Y') t ω)
        = l • (fun ω => ∑ t ∈ Finset.Icc 1 T, Y t ω) + (1 - l) • (fun ω => ∑ t ∈ Finset.Icc 1 T, Y' t ω) := by
      funext ω
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [this]
    exact hA2 T le_rfl _ _ (hSL Y hY) (hSL Y' hY') l hl0 hl1
  · intro Y Y' hY hY' hle
    rw [h347 _ hY, h347 _ hY']
    refine hA3 T le_rfl _ _ (hSL Y hY) (hSL Y' hY') ?_
    have hall : ∀ᵐ ω ∂P, ∀ t ∈ Finset.Icc 1 T, Y t ω ≤ Y' t ω :=
      (Filter.eventually_all_finset _).2 hle
    filter_upwards [hall] with ω hω
    exact Finset.sum_le_sum hω
  · intro t ht
    have ht' : t ≤ T := (Finset.mem_Icc.1 ht).2
    exact ⟨hA1 t ht', hA2 t ht', hA3 t ht'⟩
  · intro hH
    have hhom : ∀ t, t ≤ T → ∀ X : Ω → ℝ, IsLp (ℱ T) P p X → ∀ l : ℝ, 0 < l →
        compositionValue P A t (l • X) = l * compositionValue P A t X := by
      intro t ht X hX l hl
      unfold compositionValue
      rw [integral_congr_ae (g79t_comp_hom hA hH t ht X hX l hl)]
      simp [integral_const_mul]
    refine ⟨fun Y hY l hl => ?_, fun t ht => hhom t (Finset.mem_Icc.1 ht).2⟩
    have hlY : ∀ t ∈ Finset.Icc 1 T, IsLp (ℱ t) P p ((l • Y) t) := fun t ht =>
      g79t_Lsmul l (hY t ht)
    rw [h347 _ hY, h347 _ hlY]
    have : (fun ω => ∑ t ∈ Finset.Icc 1 T, (l • Y) t ω) = l • fun ω => ∑ t ∈ Finset.Icc 1 T, Y t ω := by
      funext ω; simp [Finset.mul_sum]
    rw [this]
    exact hhom T le_rfl _ (hSL Y hY) l hl
