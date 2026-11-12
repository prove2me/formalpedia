-- Prove2me | solution 1 for UniformADProbes.Trace.recover_pointed_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:33:39.050648+00:00
-- url     : https://prove2.me/submissions/3cc43ecf-8fc7-4df9-97b9-7eda5ff551e7

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra

section
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.Recover
open UniformADProbes.Trace

section abstract
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n m : ℕ}

lemma dot_eq (v w : Fin n → ℝ) : dot v w = v ⬝ᵥ w := rfl

lemma dot_lc_left (z : ι → Fin n → ℝ) (c : ι → ℝ) (w : Fin n → ℝ) :
    dot (Fintype.linearCombination ℝ z c) w = ∑ i, c i * dot (z i) w := by
  simp [Fintype.linearCombination_apply, dot_eq, sum_dotProduct, smul_dotProduct]

lemma dot_lc_right (z : ι → Fin n → ℝ) (c : ι → ℝ) (w : Fin n → ℝ) :
    dot w (Fintype.linearCombination ℝ z c) = ∑ i, c i * dot w (z i) := by
  simp [Fintype.linearCombination_apply, dot_eq, dotProduct_sum, dotProduct_smul]

lemma dot_lc_lc (z : ι → Fin n → ℝ) (z' : ι → Fin m → ℝ)
    (hG : ∀ i j, dot (z i) (z j) = dot (z' i) (z' j)) (c d : ι → ℝ) :
    dot (Fintype.linearCombination ℝ z c) (Fintype.linearCombination ℝ z d) =
      dot (Fintype.linearCombination ℝ z' c) (Fintype.linearCombination ℝ z' d) := by
  simp only [dot_lc_left, dot_lc_right, hG]

lemma ker_le (z : ι → Fin n → ℝ) (z' : ι → Fin m → ℝ)
    (hG : ∀ i j, dot (z i) (z j) = dot (z' i) (z' j)) :
    LinearMap.ker (Fintype.linearCombination ℝ z) ≤ LinearMap.ker (Fintype.linearCombination ℝ z') := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  have h := dot_lc_lc z z' hG c c
  rw [hc] at h
  have h0 : dot (0 : Fin n → ℝ) 0 = 0 := by simp [dot_eq]
  rw [h0] at h
  have := (dotProduct_self_eq_zero).1 (show _ ⬝ᵥ _ = 0 from h.symm)
  exact this

lemma exists_equiv (z : ι → Fin n → ℝ) (z' : ι → Fin m → ℝ)
    (hG : ∀ i j, dot (z i) (z j) = dot (z' i) (z' j)) :
    ∃ e : Submodule.span ℝ (Set.range z) ≃ₗ[ℝ] Submodule.span ℝ (Set.range z'),
      (∀ c (h : Fintype.linearCombination ℝ z c ∈ Submodule.span ℝ (Set.range z))
          (h' : Fintype.linearCombination ℝ z' c ∈ Submodule.span ℝ (Set.range z')),
        e ⟨Fintype.linearCombination ℝ z c, h⟩ = ⟨Fintype.linearCombination ℝ z' c, h'⟩) := by
  set f := Fintype.linearCombination ℝ z with hf
  set g := Fintype.linearCombination ℝ z' with hg
  have hker : LinearMap.ker f = LinearMap.ker g :=
    le_antisymm (ker_le z z' hG) (ker_le z' z (fun i j => (hG i j).symm))
  have hr : Submodule.span ℝ (Set.range z) = LinearMap.range f := by
    rw [hf, Fintype.range_linearCombination]
  have hr' : Submodule.span ℝ (Set.range z') = LinearMap.range g := by
    rw [hg, Fintype.range_linearCombination]
  let e0 : LinearMap.range f ≃ₗ[ℝ] LinearMap.range g :=
    (f.quotKerEquivRange).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans g.quotKerEquivRange)
  refine ⟨(LinearEquiv.ofEq _ _ hr).trans (e0.trans (LinearEquiv.ofEq _ _ hr'.symm)), ?_⟩
  intro c h h'
  apply Subtype.ext
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, e0]
  have : f.quotKerEquivRange.symm ⟨f c, LinearMap.mem_range_self f c⟩ =
      (LinearMap.ker f).mkQ c := LinearMap.quotKerEquivRange_symm_apply_image f c _
  show (g.quotKerEquivRange ((Submodule.quotEquivOfEq _ _ hker)
      (f.quotKerEquivRange.symm ⟨f c, _⟩)) : Fin m → ℝ) = g c
  rw [this]
  simp [LinearMap.quotKerEquivRange_apply_mk]

lemma intertwine (z : ι → Fin n → ℝ) (z' : ι → Fin m → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (M' : Matrix (Fin m) (Fin m) ℝ)
    (hG : ∀ i j, dot (z i) (z j) = dot (z' i) (z' j))
    (hM : ∀ j, M.mulVec (z j) ∈ Submodule.span ℝ (Set.range z))
    (hM' : ∀ j, M'.mulVec (z' j) ∈ Submodule.span ℝ (Set.range z'))
    (hGM : ∀ i j, dot (z i) (M.mulVec (z j)) = dot (z' i) (M'.mulVec (z' j)))
    (e : Submodule.span ℝ (Set.range z) ≃ₗ[ℝ] Submodule.span ℝ (Set.range z'))
    (he : ∀ c (h : Fintype.linearCombination ℝ z c ∈ Submodule.span ℝ (Set.range z))
          (h' : Fintype.linearCombination ℝ z' c ∈ Submodule.span ℝ (Set.range z')),
        e ⟨Fintype.linearCombination ℝ z c, h⟩ = ⟨Fintype.linearCombination ℝ z' c, h'⟩) :
    ∀ u : Submodule.span ℝ (Set.range z),
      ∃ h : M.mulVec u.val ∈ Submodule.span ℝ (Set.range z),
        (e ⟨M.mulVec u.val, h⟩).val = M'.mulVec (e u).val := by
  set f := Fintype.linearCombination ℝ z with hf
  set g := Fintype.linearCombination ℝ z' with hg
  have hmemf : ∀ w ∈ Submodule.span ℝ (Set.range z), ∃ c, f c = w := by
    intro w hw
    rw [← Fintype.range_linearCombination ℝ z] at hw
    exact hw
  have hmemg : ∀ w ∈ Submodule.span ℝ (Set.range z'), ∃ c, g c = w := by
    intro w hw
    rw [← Fintype.range_linearCombination ℝ z'] at hw
    exact hw
  have hfsingle : ∀ i, f (Pi.single i 1) = z i := by
    intro i; simp [hf]
  have hgsingle : ∀ i, g (Pi.single i 1) = z' i := by
    intro i; simp [hg]
  choose a ha using fun j => hmemf _ (hM j)
  have key : ∀ j, g (a j) = M'.mulVec (z' j) := by
    intro j
    obtain ⟨b, hb⟩ := hmemg (g (a j) - M'.mulVec (z' j))
      (Submodule.sub_mem _ (by rw [← Fintype.range_linearCombination ℝ z']; exact ⟨_, rfl⟩) (hM' j))
    have hi : ∀ i, dot (z' i) (g (a j) - M'.mulVec (z' j)) = 0 := by
      intro i
      have h1 : dot (z' i) (g (a j)) = dot (z' i) (M'.mulVec (z' j)) := by
        have := dot_lc_lc z z' hG (Pi.single i 1) (a j)
        rw [← hf, ← hg, hfsingle, hgsingle, ha] at this
        rw [← this]; exact hGM i j
      simp only [dot_eq] at h1 ⊢
      rw [dotProduct_sub, h1, sub_self]
    have hd : dot (g (a j) - M'.mulVec (z' j)) (g (a j) - M'.mulVec (z' j)) = 0 := by
      nth_rewrite 1 [← hb]
      rw [show dot (g b) (g (a j) - M'.mulVec (z' j)) =
        ∑ i, b i * dot (z' i) (g (a j) - M'.mulVec (z' j)) from dot_lc_left z' b _]
      simp [hi]
    have := (dotProduct_self_eq_zero).1 (show _ ⬝ᵥ _ = 0 from hd)
    exact sub_eq_zero.1 this
  intro u
  obtain ⟨c, hc⟩ := hmemf u.val u.2
  have hu : u = ⟨f c, by rw [hc]; exact u.2⟩ := Subtype.ext hc.symm
  have hmf : M.mulVec (f c) = f (∑ j, c j • a j) := by
    simp [hf, Fintype.linearCombination_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, ← ha]
  have hmg : M'.mulVec (g c) = g (∑ j, c j • a j) := by
    simp [hg, Fintype.linearCombination_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, ← key]
  have hmem : M.mulVec u.val ∈ Submodule.span ℝ (Set.range z) := by
    rw [← hc, hmf, ← Fintype.range_linearCombination ℝ z]; exact ⟨_, rfl⟩
  refine ⟨hmem, ?_⟩
  have h1 : (⟨M.mulVec u.val, hmem⟩ : Submodule.span ℝ (Set.range z)) =
      ⟨f (∑ j, c j • a j), by rw [← hmf, hc]; exact hmem⟩ := by
    apply Subtype.ext; simp only [← hc, hmf]
  have h2 : e u = ⟨g c, by rw [← Fintype.range_linearCombination ℝ z']; exact ⟨_, rfl⟩⟩ := by
    rw [hu]; exact he c _ _
  rw [h1, he _ _ (by rw [← Fintype.range_linearCombination ℝ z']; exact ⟨_, rfl⟩), h2]
  exact hmg.symm

lemma dot_pres (z : ι → Fin n → ℝ) (z' : ι → Fin m → ℝ)
    (hG : ∀ i j, dot (z i) (z j) = dot (z' i) (z' j))
    (e : Submodule.span ℝ (Set.range z) ≃ₗ[ℝ] Submodule.span ℝ (Set.range z'))
    (he : ∀ c (h : Fintype.linearCombination ℝ z c ∈ Submodule.span ℝ (Set.range z))
          (h' : Fintype.linearCombination ℝ z' c ∈ Submodule.span ℝ (Set.range z')),
        e ⟨Fintype.linearCombination ℝ z c, h⟩ = ⟨Fintype.linearCombination ℝ z' c, h'⟩) :
    ∀ u w, dot (e u).val (e w).val = dot u.val w.val := by
  have hmemf : ∀ w ∈ Submodule.span ℝ (Set.range z), ∃ c, Fintype.linearCombination ℝ z c = w := by
    intro w hw
    rw [← Fintype.range_linearCombination ℝ z] at hw
    exact hw
  intro u w
  obtain ⟨c, hc⟩ := hmemf u.val u.2
  obtain ⟨d, hd⟩ := hmemf w.val w.2
  have hu : u = ⟨Fintype.linearCombination ℝ z c, by rw [hc]; exact u.2⟩ := Subtype.ext hc.symm
  have hw : w = ⟨Fintype.linearCombination ℝ z d, by rw [hd]; exact w.2⟩ := Subtype.ext hd.symm
  have h1 := he c (by rw [hc]; exact u.2) (by rw [← Fintype.range_linearCombination ℝ z']; exact ⟨_, rfl⟩)
  have h2 := he d (by rw [hd]; exact w.2) (by rw [← Fintype.range_linearCombination ℝ z']; exact ⟨_, rfl⟩)
  rw [hu, hw, h1, h2]
  exact (dot_lc_lc z z' hG c d).symm

end abstract

section main

lemma polyEval_one {R : Type} [Ring R] (H K : R) : polyEval H K (1 : NCPoly) = 1 := by
  simp [polyEval, MonoidAlgebra.one_def, wordEval]

lemma cyc_closed {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (b : Bool)
    (u : Fin n → ℝ) (hu : u ∈ cyclicModule H K v) :
    (if b then K else H).mulVec u ∈ cyclicModule H K v := by
  unfold cyclicModule at hu ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨w, rfl⟩
    apply Submodule.subset_span
    refine ⟨FreeMonoid.ofList (b :: w.toList), ?_⟩
    simp [wordEval, Matrix.mulVec_mulVec]
  · simp
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

lemma recover_main (n m : ℕ)
    (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (H' K' : Matrix (Fin m) (Fin m) ℝ) (v' : Fin m → ℝ)
    (U : List NCPoly) (hzero : U.head? = some 1)
    (hspan : responseSpan H K v U = cyclicModule H K v)
    (hspan' : responseSpan H' K' v' U = cyclicModule H' K' v')
    (hgram : gramData H K v U = gramData H' K' v' U) :
    PointedEquivalent H K v H' K' v' := by
  let z : Fin U.length → Fin n → ℝ := fun i => (polyEval H K U[i]).mulVec v
  let z' : Fin U.length → Fin m → ℝ := fun i => (polyEval H' K' U[i]).mulVec v'
  have hrs : ∀ {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (w : Fin k → ℝ),
      responseSpan A B w U = Submodule.span ℝ (Set.range fun i : Fin U.length =>
        (polyEval A B U[i]).mulVec w) := by
    intro k A B w
    unfold responseSpan
    congr 1
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨i, hi, hp2⟩ := List.getElem_of_mem hp
      subst hp2
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨U[i], List.getElem_mem _, rfl⟩
  have hc : cyclicModule H K v = Submodule.span ℝ (Set.range z) := by
    rw [← hspan, hrs]
  have hc' : cyclicModule H' K' v' = Submodule.span ℝ (Set.range z') := by
    rw [← hspan', hrs]
  have hgs : ∀ (s : Fin 3) (i j : Fin U.length),
      dot (z i) ((if s.val = 0 then 1 else if s.val = 1 then H else K).mulVec (z j)) =
      dot (z' i) ((if s.val = 0 then 1 else if s.val = 1 then H' else K').mulVec (z' j)) := by
    intro s i j
    have := congrFun (congrFun (congrFun hgram s) i) j
    simpa [gramData, z, z'] using this
  have hG : ∀ i j, dot (z i) (z j) = dot (z' i) (z' j) := by
    intro i j
    simpa using hgs 0 i j
  have hGH : ∀ i j, dot (z i) (H.mulVec (z j)) = dot (z' i) (H'.mulVec (z' j)) := by
    intro i j
    simpa using hgs 1 i j
  have hGK : ∀ i j, dot (z i) (K.mulVec (z j)) = dot (z' i) (K'.mulVec (z' j)) := by
    intro i j
    simpa using hgs 2 i j
  have hzmem : ∀ j, z j ∈ cyclicModule H K v := by
    intro j; rw [hc]; exact Submodule.subset_span ⟨j, rfl⟩
  have hzmem' : ∀ j, z' j ∈ cyclicModule H' K' v' := by
    intro j; rw [hc']; exact Submodule.subset_span ⟨j, rfl⟩
  have hHz : ∀ j, H.mulVec (z j) ∈ Submodule.span ℝ (Set.range z) := by
    intro j; rw [← hc]; simpa using cyc_closed H K v false _ (hzmem j)
  have hKz : ∀ j, K.mulVec (z j) ∈ Submodule.span ℝ (Set.range z) := by
    intro j; rw [← hc]; simpa using cyc_closed H K v true _ (hzmem j)
  have hHz' : ∀ j, H'.mulVec (z' j) ∈ Submodule.span ℝ (Set.range z') := by
    intro j; rw [← hc']; simpa using cyc_closed H' K' v' false _ (hzmem' j)
  have hKz' : ∀ j, K'.mulVec (z' j) ∈ Submodule.span ℝ (Set.range z') := by
    intro j; rw [← hc']; simpa using cyc_closed H' K' v' true _ (hzmem' j)
  obtain ⟨e, he⟩ := exists_equiv z z' hG
  have hdot := dot_pres z z' hG e he
  have hIH := intertwine z z' H H' hG hHz hHz' hGH e he
  have hIK := intertwine z z' K K' hG hKz hKz' hGK e he
  -- seed
  have hne : 0 < U.length := by
    rcases U with _ | ⟨a, U⟩
    · simp at hzero
    · simp
  have hU0 : U[0]'hne = 1 := by
    rcases U with _ | ⟨a, U⟩
    · simp at hzero
    · simpa using hzero
  have hz0 : z ⟨0, hne⟩ = v := by simp [z, hU0, polyEval_one]
  have hz0' : z' ⟨0, hne⟩ = v' := by simp [z', hU0, polyEval_one]
  refine ⟨(LinearEquiv.ofEq _ _ hc).trans (e.trans (LinearEquiv.ofEq _ _ hc'.symm)), ?_, ?_, ?_⟩
  · intro u w
    exact hdot ⟨u.val, hc ▸ u.2⟩ ⟨w.val, hc ▸ w.2⟩
  · have hvm : v ∈ cyclicModule H K v := hz0 ▸ hzmem ⟨0, hne⟩
    have hvm' : v' ∈ cyclicModule H' K' v' := hz0' ▸ hzmem' ⟨0, hne⟩
    refine ⟨hvm, hvm', ?_⟩
    apply Subtype.ext
    have := he (Pi.single ⟨0, hne⟩ 1)
      (by rw [← Fintype.range_linearCombination ℝ z]; exact ⟨_, rfl⟩)
      (by rw [← Fintype.range_linearCombination ℝ z']; exact ⟨_, rfl⟩)
    have h1 : Fintype.linearCombination ℝ z (Pi.single ⟨0, hne⟩ 1) = v := by simp [hz0]
    have h2 : Fintype.linearCombination ℝ z' (Pi.single ⟨0, hne⟩ 1) = v' := by simp [hz0']
    have h3 := congrArg Subtype.val this
    simp only [h1, h2] at h3
    exact h3
  · intro u
    obtain ⟨hH, hH2⟩ := hIH ⟨u.val, hc ▸ u.2⟩
    obtain ⟨hK, hK2⟩ := hIK ⟨u.val, hc ▸ u.2⟩
    have hHm : H.mulVec u.val ∈ cyclicModule H K v := by
      simpa using cyc_closed H K v false u.val u.2
    have hKm : K.mulVec u.val ∈ cyclicModule H K v := by
      simpa using cyc_closed H K v true u.val u.2
    refine ⟨hHm, hKm, ?_, ?_⟩
    · exact hH2
    · exact hK2

end main

end UniformADProbes.Trace.Dev.Recover

namespace UniformADProbes.Trace
open UniformADProbes.Trace.Dev.Recover in
theorem chk_recover_pointed_representation (n m : ℕ)
    (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (H' K' : Matrix (Fin m) (Fin m) ℝ) (v' : Fin m → ℝ)
    (hH : H.IsSymm) (hK : K.IsSymm) (hH' : H'.IsSymm) (hK' : K'.IsSymm)
    (U : List NCPoly) (hzero : U.head? = some 1)
    (hspan : responseSpan H K v U = cyclicModule H K v)
    (hspan' : responseSpan H' K' v' U = cyclicModule H' K' v')
    (hgram : gramData H K v U = gramData H' K' v' U) :
    PointedEquivalent H K v H' K' v' :=
  recover_main n m H K v H' K' v' U hzero hspan hspan' hgram

end UniformADProbes.Trace
end

theorem solution : type_of% @UniformADProbes.Trace.chk_recover_pointed_representation := @UniformADProbes.Trace.chk_recover_pointed_representation
