-- Prove2me | solution 1 for connected_simple_arc_attachment_no_continuous_log
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T03:14:15.626904+00:00
-- url     : https://prove2.me/submissions/15dfe0b5-8dd3-4a98-bab5-c1385d22a405

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Set

/-- The fiber of the complex exponential over one is countable. -/
lemma complex_exp_one_fiber_countable : {z : ℂ | Complex.exp z = 1}.Countable := by
  apply (Set.countable_range (fun n : ℤ => (n : ℂ) * (2 * Real.pi * Complex.I))).mono
  intro z hz
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hz
  exact ⟨n, hn.symm⟩

/-- Two continuous lifts with equal exponentials differ by a constant on a preconnected set. -/
lemma exp_lifts_diff_constant_on_preconnected {X : Type} [TopologicalSpace X]
    (W : Set X) (f g : X → ℂ) (hW : IsPreconnected W)
    (hf : ContinuousOn f W) (hg : ContinuousOn g W)
    (heq : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (g x)) W)
    (p : X) (hp : p ∈ W) :
    ∀ x ∈ W, f x - g x = f p - g p := by
  let H : X → ℂ := fun x => f x - g x
  have hH : ContinuousOn H W := hf.sub hg
  have hconnected : IsPreconnected (H '' W) := hW.image H hH
  have hsubset : H '' W ⊆ {z : ℂ | Complex.exp z = 1} := by
    rintro z ⟨x, hx, rfl⟩
    change Complex.exp (f x - g x) = 1
    exact Complex.exp_eq_exp_iff_exp_sub_eq_one.mp (heq hx)
  have hsub : (H '' W).Subsingleton :=
    complex_exp_one_fiber_countable.isTotallyDisconnected _ hsubset hconnected
  intro x hx
  exact hsub ⟨x, hx, rfl⟩ ⟨p, hp, rfl⟩

/-- A logarithm cannot be single-valued on a connected attachment when its
exponential winds once along the attached arc and is one on K. -/
theorem connected_attachment_winding_no_log
    {X : Type} [TopologicalSpace X] (K : Set X) (a : ℝ → X)
    (hc : ContinuousOn a (Icc (0 : ℝ) 1))
    (hsame : a 1 ∈ connectedComponentIn K (a 0))
    (F : X → ℂ) (hFK : EqOn F (fun _ => 1) K)
    (hFA : ∀ t ∈ Icc (0 : ℝ) 1,
      F (a t) = Complex.exp ((t : ℂ) * (2 * Real.pi * Complex.I))) :
    ¬ ∃ f : X → ℂ, ContinuousOn f (K ∪ a '' Icc (0 : ℝ) 1) ∧
      EqOn (fun x => Complex.exp (f x)) F (K ∪ a '' Icc (0 : ℝ) 1) := by
  rintro ⟨f, hf, he⟩
  let W := connectedComponentIn K (a 0)
  have h0K : a 0 ∈ K := connectedComponentIn_nonempty_iff.mp ⟨a 1, hsame⟩
  have h0W : a 0 ∈ W := mem_connectedComponentIn h0K
  have h1W : a 1 ∈ W := hsame
  have hWK : W ⊆ K := connectedComponentIn_subset K (a 0)
  have hfW : ContinuousOn f W := hf.mono (hWK.trans subset_union_left)
  have heW : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (0 : ℂ)) W := by
    intro x hx
    have hh : Complex.exp (f x) = F x := he (Or.inl (hWK hx))
    change Complex.exp (f x) = Complex.exp (0 : ℂ)
    rw [hh, hFK (hWK hx), Complex.exp_zero]
  have hconst := exp_lifts_diff_constant_on_preconnected W f (fun _ => 0)
    isPreconnected_connectedComponentIn hfW continuousOn_const heW (a 0) h0W (a 1) h1W
  have hequal : f (a 1) = f (a 0) := by simpa using hconst
  let g : ℝ → ℂ := fun t => (t : ℂ) * (2 * Real.pi * Complex.I)
  have hfg : ContinuousOn (fun t => f (a t)) (Icc (0 : ℝ) 1) :=
    hf.comp hc (fun t ht => Or.inr ⟨t, ht, rfl⟩)
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) :=
    (Complex.continuous_ofReal.mul continuous_const).continuousOn
  have heq : EqOn (fun t => Complex.exp (f (a t))) (fun t => Complex.exp (g t))
      (Icc (0 : ℝ) 1) := by
    intro t ht
    have h := he (Or.inr ⟨t, ht, rfl⟩)
    exact h.trans (hFA t ht)
  have hloop := exp_lifts_diff_constant_on_preconnected (Icc (0 : ℝ) 1)
    (fun t => f (a t)) g isPreconnected_Icc hfg hgc heq 0 ⟨le_rfl, zero_le_one⟩
    1 ⟨zero_le_one, le_rfl⟩
  rw [hequal] at hloop
  have hperiod : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  apply hperiod
  simpa [g] using (sub_right_inj.mp hloop).symm

/-- A simple compact arc carries the standard once-around exponential loop. -/
theorem simple_arc_winding_map {X : Type} [TopologicalSpace X] [T2Space X]
    (a : ℝ → X) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hi : InjOn a (Icc (0 : ℝ) 1)) :
    ∃ g : X → ℂ, ContinuousOn g (a '' Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, g (a t) =
        Complex.exp ((t : ℂ) * (2 * Real.pi * Complex.I)) := by
  classical
  let I := Icc (0 : ℝ) 1
  let f : I → X := I.domRestrict a
  let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  have hfcont : Continuous f := ha.domRestrict
  have hfinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact hi x.property y.property h
  have hf : Topology.IsEmbedding f := (hfcont.isClosedEmbedding hfinj).isEmbedding
  let e := hf.toHomeomorph
  let g : X → ℂ := fun x => if hx : x ∈ range f then
    Complex.exp (((e.symm ⟨x, hx⟩).1 : ℂ) * (2 * Real.pi * Complex.I)) else 1
  refine ⟨g, ?_, ?_⟩
  · have hc : Continuous (fun x : range f =>
        Complex.exp (((e.symm x).1 : ℂ) * (2 * Real.pi * Complex.I))) :=
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp e.symm.continuous)).mul continuous_const))
    have hgc : ContinuousOn g (range f) := by
      rw [continuousOn_iff_continuous_domRestrict]
      convert hc using 1
      funext x
      change g x = _
      simp only [g, dif_pos x.property]
    simpa only [f, I, Set.range_domRestrict] using hgc
  · intro t ht
    have hmem : a t ∈ range f := ⟨⟨t, ht⟩, rfl⟩
    have he : e.symm ⟨a t, hmem⟩ = ⟨t, ht⟩ := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      rfl
    simp only [g, dif_pos hmem, he]

#print axioms simple_arc_winding_map

/-- An attached simple arc determines a nowhere-zero winding map on the union. -/
theorem attached_arc_winding_map {X : Type} [TopologicalSpace X] [T2Space X]
    (K : Set X) (a : ℝ → X) (hK : IsCompact K)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hi : InjOn a (Icc (0 : ℝ) 1))
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K) :
    ∃ F : X → ℂ, ContinuousOn F (K ∪ a '' Icc (0 : ℝ) 1) ∧
      (∀ z ∈ K ∪ a '' Icc (0 : ℝ) 1, F z ≠ 0) ∧
      EqOn F (fun _ => 1) K ∧
      ∀ t ∈ Icc (0 : ℝ) 1, F (a t) =
        Complex.exp ((t : ℂ) * (2 * Real.pi * Complex.I)) := by
  classical
  obtain ⟨g, hgc, hg⟩ := simple_arc_winding_map a ha hi
  let A := a '' Icc (0 : ℝ) 1
  have hA : IsClosed A := (isCompact_Icc.image_of_continuousOn ha).isClosed
  have hagree : ∀ z ∈ K ∩ A, g z = 1 := by
    rintro z ⟨hzK, t, ht, rfl⟩
    have hend : t = 0 ∨ t = 1 := by
      by_contra h
      push Not at h
      exact hinterior t ⟨lt_of_le_of_ne ht.1 (Ne.symm h.1),
        lt_of_le_of_ne ht.2 h.2⟩ hzK
    rcases hend with rfl | rfl
    · simpa using hg 0 ⟨le_rfl, zero_le_one⟩
    · simpa [Complex.exp_two_pi_mul_I] using hg 1 ⟨zero_le_one, le_rfl⟩
  let F : X → ℂ := K.piecewise (fun _ => 1) g
  have hFK : EqOn F (fun _ => 1) K := by
    intro z hz
    simp [F, hz]
  have hFA : EqOn F g A := by
    intro z hz
    by_cases hzK : z ∈ K
    · simpa [F, hzK] using (hagree z ⟨hzK, hz⟩).symm
    · simp [F, hzK]
  have hFcK : ContinuousOn F K := continuousOn_const.congr hFK
  have hFcA : ContinuousOn F A := hgc.congr hFA
  have hFval : ∀ t ∈ Icc (0 : ℝ) 1, F (a t) =
      Complex.exp ((t : ℂ) * (2 * Real.pi * Complex.I)) := by
    intro t ht
    exact (hFA ⟨t, ht, rfl⟩).trans (hg t ht)
  refine ⟨F, hFcK.union_of_isClosed hFcA hK.isClosed hA, ?_, hFK, hFval⟩
  intro z hz
  rcases hz with hz | ⟨t, ht, rfl⟩
  · rw [hFK hz]; exact one_ne_zero
  · rw [hFval t ht]; exact Complex.exp_ne_zero _

#print axioms attached_arc_winding_map

/-- The winding map on an arc attached to one component has no continuous logarithm. -/
theorem solution {X : Type} [TopologicalSpace X] [T2Space X]
    (K : Set X) (a : ℝ → X) (hK : IsCompact K)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hi : InjOn a (Icc (0 : ℝ) 1))
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (hsame : a 1 ∈ connectedComponentIn K (a 0)) :
    ∃ F : X → ℂ, ContinuousOn F (K ∪ a '' Icc (0 : ℝ) 1) ∧
      (∀ z ∈ K ∪ a '' Icc (0 : ℝ) 1, F z ≠ 0) ∧
      ¬ ∃ f : X → ℂ, ContinuousOn f (K ∪ a '' Icc (0 : ℝ) 1) ∧
        EqOn (fun x => Complex.exp (f x)) F (K ∪ a '' Icc (0 : ℝ) 1) := by
  obtain ⟨F, hFc, hFne, hFK, hFA⟩ := attached_arc_winding_map K a hK ha hi hinterior
  exact ⟨F, hFc, hFne, connected_attachment_winding_no_log K a ha hsame F hFK hFA⟩

#print axioms solution
