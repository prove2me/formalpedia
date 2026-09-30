-- Prove2me | solution 1 for PhilipponMultiplicity.iterated_jet_sections_eq_differentialIdeal
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T10:47:05.322098+00:00
-- url     : https://prove2.me/submissions/02702c17-58ea-411d-b0a9-9d52b99ec57f

import Theorems.Thm_PhilipponMultiplicity_normalized_jet_translation_germ
import Definitions.Def_PhilipponMultiplicity_IteratedJets
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter MvPolynomial
noncomputable section
open scoped ContDiff

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- Ordered directional differentiation; the head direction is applied last. -/
def mixedDeriv : List E → (E → K) → E → K
  | [], f => f
  | v :: w, f => fun x => fderiv K (mixedDeriv w f) x v

theorem mixedDeriv_analytic {f : E → K} {x : E} (hf : AnalyticAt K f x)
    (w : List E) : AnalyticAt K (mixedDeriv w f) x := by
  induction w with
  | nil => exact hf
  | cons v w ih =>
    exact ((ContinuousLinearMap.apply K K v).analyticAt _).comp ih.fderiv

theorem mixedDeriv_congr {f g : E → K} {x : E} (h : f =ᶠ[𝓝 x] g)
    (w : List E) : mixedDeriv w f =ᶠ[𝓝 x] mixedDeriv w g := by
  induction w with
  | nil => exact h
  | cons v w ih =>
    filter_upwards [ih.fderiv (𝕜 := K)] with y hy
    exact congrArg (fun L : E →L[K] K => L v) hy

theorem mixedDeriv_eq_iteratedFDeriv {f : E → K} {x : E}
    (hf : AnalyticAt K f x) (w : List E) :
    mixedDeriv w f x = iteratedFDeriv K w.length f x w.get := by
  induction w generalizing x with
  | nil => simp [mixedDeriv]
  | cons v w ih =>
    have hn : (mixedDeriv w f) =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv K w.length f y w.get) := by
      have he : ∀ᶠ y in 𝓝 x, AnalyticAt K f y := hf.eventually_analyticAt
      filter_upwards [he] with y hy
      exact ih hy
    change fderiv K (mixedDeriv w f) x v = _
    rw [hn.fderiv_eq]
    have hd := (hf.contDiffAt : ContDiffAt K (⊤ : ℕ∞ω) f x).differentiableAt_iteratedFDeriv
      (m := w.length) (by simp)
    have htail : Fin.tail (v::w).get = w.get := by funext i; rfl
    simpa only [List.length_cons,htail,List.get_cons_zero] using
      (hd.iteratedFDeriv_succ_apply_left' (m := (v::w).get)).symm

theorem iteratedFDeriv_apply_congr {n m : ℕ} (h : n = m) (f : E → K) (x : E)
    (v : Fin n → E) (w : Fin m → E) (hv : ∀ i, v i = w (Fin.cast h i)) :
    iteratedFDeriv K n f x v = iteratedFDeriv K m f x w := by
  subst m
  congr 1
  funext i
  exact hv i

theorem mixedDeriv_map_eq_iteratedFDeriv {ι : Type*} (v : ι → E)
    {f : E → K} {x : E} (hf : AnalyticAt K f x) (w : List ι) :
    mixedDeriv (w.map v) f x = iteratedFDeriv K w.length f x (fun i => v (w.get i)) := by
  rw [mixedDeriv_eq_iteratedFDeriv hf]
  apply iteratedFDeriv_apply_congr (List.length_map ..)
  intro i
  simp


end PhilipponMultiplicity.JetSupport

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

theorem mixedDeriv_append (u v : List E) (f : E → K) :
    mixedDeriv (u ++ v) f = mixedDeriv u (mixedDeriv v f) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, mixedDeriv, ih]

theorem mixedDeriv_comp_add_left (w : List E) (f : E → K) (a : E) :
    mixedDeriv w (fun z => f (a + z)) = fun z => mixedDeriv w f (a + z) := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    funext z
    simp only [mixedDeriv, ih, fderiv_comp_add_left]

end PhilipponMultiplicity.JetSupport

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem projective_pivot_ne_zero {ι : Type*} (v : ι → K) (hv : v ≠ 0)
    (p : Projectivization K (ι → K)) (hp : Projectivization.mk K v hv = p)
    (j : ι) (hj : p.rep j ≠ 0) : v j ≠ 0 := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v p.rep hv p.rep_nonzero).mp
    (hp.trans p.mk_rep.symm)
  have hj' : v j = (a : K) * p.rep j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  rw [hj']
  exact mul_ne_zero a.ne_zero hj

theorem projective_pivot_ne_zero_iff {ι : Type*} (v : ι → K) (hv : v ≠ 0)
    (p : Projectivization K (ι → K)) (hp : Projectivization.mk K v hv = p)
    (j : ι) : v j ≠ 0 ↔ p.rep j ≠ 0 := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v p.rep hv p.rep_nonzero).mp
    (hp.trans p.mk_rep.symm)
  have hj : v j = (a : K) * p.rep j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  simp [hj,a.ne_zero]

theorem lift_pivot_ne_zero (A : AnalyticSubgroup G) (g : G.Point)
    (b : CoordinateChart G) (hg : g ∈ chartDomain G b) (i : G.FactorIndex) :
    A.lift g 0 ⟨i,b i⟩ ≠ 0 := by
  obtain ⟨hz,hi⟩ := (A.lift_represents g).self_of_nhds
  have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  rw [hz',A.map_zero,add_zero] at hi
  obtain ⟨hne,heq⟩ := hi i
  exact projective_pivot_ne_zero _ hne _ heq _ (hg i)

theorem normalizedPullback_analytic (A : AnalyticSubgroup G) (g : G.Point)
    (b : CoordinateChart G) (P : G.CoordinateRing) (x : G.Point)
    (hx : g + x ∈ chartDomain G b) :
    AnalyticAt K (normalizedPullback A g b P x) 0 := by
  apply AnalyticAt.aeval_mvPolynomial
  intro v
  exact (A.lift_analytic (g+x) v).div (A.lift_analytic (g+x) ⟨v.1,b v.1⟩)
    (lift_pivot_ne_zero A (g+x) b hx v.1)


end PhilipponMultiplicity.OperatorSupport

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}
theorem normalizedJet_translate_germ (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    {T : ℕ} (j : JetIndex A.parameterDimension T) :
    (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
      normalizedJet A g' b P j (g + x + A.map ⟨z,hz⟩) else 0) =ᶠ[𝓝 0]
      (fun z => iteratedFDeriv K j.order (normalizedPullback A (g+g') b P x) z
        (fun i => Pi.single (j.directions i) 1)) := by
  exact PhilipponMultiplicity.normalized_jet_translation_germ K G A g g' x b P T j
theorem normalizedJet_composition (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    (hx : g + g' + x ∈ chartDomain G b)
    (u v : List (Fin A.parameterDimension)) :
    JetSupport.mixedDeriv (u.map (fun i => Pi.single i (1 : K)))
      (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
        normalizedJet A g' b P
          (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
          (g + x + A.map ⟨z,hz⟩) else 0) 0 =
      JetSupport.mixedDeriv ((u ++ v).map (fun i => Pi.single i (1 : K)))
        (normalizedPullback A (g + g') b P x) 0 := by
  have ha := normalizedPullback_analytic A (g+g') b P x hx
  have he := normalizedJet_translate_germ A g g' x b P
    (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
  have hv : (fun z => iteratedFDeriv K v.length (normalizedPullback A (g+g') b P x) z
      (fun i => Pi.single (v.get i) (1 : K))) =ᶠ[𝓝 0]
      JetSupport.mixedDeriv (v.map (fun i => Pi.single i (1 : K)))
        (normalizedPullback A (g+g') b P x) := by
    filter_upwards [ha.eventually_analyticAt] with z hz
    exact (JetSupport.mixedDeriv_map_eq_iteratedFDeriv
      (fun i : Fin A.parameterDimension => Pi.single i (1 : K)) hz v).symm
  rw [List.map_append,JetSupport.mixedDeriv_append]
  exact (JetSupport.mixedDeriv_congr (he.trans hv) _).self_of_nhds

theorem normalizedJet_composition_finite (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    (hx : g + g' + x ∈ chartDomain G b)
    (u v : List (Fin A.parameterDimension)) :
    iteratedFDeriv K u.length
      (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
        normalizedJet A g' b P
          (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
          (g + x + A.map ⟨z,hz⟩) else 0) 0
        (fun i => Pi.single (u.get i) 1) =
      normalizedJet A (g+g') b P
        (⟨(u++v).length,le_rfl,(u++v).get⟩ :
          JetIndex A.parameterDimension (u++v).length) x := by
  have ha := normalizedPullback_analytic A (g+g') b P x hx
  have he := normalizedJet_translate_germ A g g' x b P
    (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
  have hv : (fun z => iteratedFDeriv K v.length (normalizedPullback A (g+g') b P x) z
      (fun i => Pi.single (v.get i) (1 : K))) =ᶠ[𝓝 0]
      JetSupport.mixedDeriv (v.map (fun i => Pi.single i (1 : K)))
        (normalizedPullback A (g+g') b P x) := by
    filter_upwards [ha.eventually_analyticAt] with z hz
    exact (JetSupport.mixedDeriv_map_eq_iteratedFDeriv
      (fun i : Fin A.parameterDimension => Pi.single i (1 : K)) hz v).symm
  have hf := (JetSupport.mixedDeriv_analytic ha
    (v.map (fun i => Pi.single i (1 : K)))).congr (he.trans hv).symm
  rw [← JetSupport.mixedDeriv_map_eq_iteratedFDeriv
    (fun i : Fin A.parameterDimension => Pi.single i (1 : K)) hf u,
    normalizedJet_composition A g g' x b P hx u v]
  exact JetSupport.mixedDeriv_map_eq_iteratedFDeriv
    (fun i : Fin A.parameterDimension => Pi.single i (1 : K)) ha (u++v)

end PhilipponMultiplicity.OperatorSupport

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

/-- Replacing a local generator by an equal section on its domain preserves
local ideal membership. Equality outside the domain is unnecessary. -/
theorem locallyGeneratedIdeal_le_of_section_replacements
    (S T : Set (LocalSection G))
    (h : ∀ f : S, ∃ t : T, f.val.domain ⊆ t.val.domain ∧
      ∀ x ∈ f.val.domain, f.val.value x = t.val.value x) :
    locallyGeneratedIdeal G S ≤ locallyGeneratedIdeal G T := by
  classical
  apply Ideal.span_le.mpr
  rintro P ⟨hP,hlocal⟩
  apply Ideal.subset_span
  refine ⟨hP,?_⟩
  intro x
  obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := hlocal x
  choose t hdom hval using (fun i => h (f i))
  refine ⟨b,U,hU,hx,hUb,n,t,r,?_,?_⟩
  · intro i y hy
    exact ⟨hdom i (hfr i y hy).1,(hfr i y hy).2⟩
  · intro y hy
    rw [heq y hy]
    apply Finset.sum_congr rfl
    intro i _
    rw [hval i y (hfr i y hy).1]

variable [CompleteSpace K]

/-- The ideal generated by the paper's two-parameter jets is exactly the
ideal generated by jets of total order at most the sum. -/
theorem iterated_jet_sections_eq_differentialIdeal
    (A : AnalyticSubgroup G) (g g' : G.Point) (T T' : ℕ) (I : Ideal G.CoordinateRing) :
    locallyGeneratedIdeal G (iteratedDifferentialSections A g g' T T' I) =
      differentialIdeal A (g+g') (T+T') I := by
  apply le_antisymm
  · apply locallyGeneratedIdeal_le_of_section_replacements
    rintro ⟨f,P,hPI,hP,b,u,hu,v,hv,rfl⟩
    let j : JetIndex A.parameterDimension (T+T') :=
      ⟨(u++v).length,by simpa only [List.length_append] using Nat.add_le_add hu hv,(u++v).get⟩
    refine ⟨⟨⟨{x | g+g'+x ∈ chartDomain G b},normalizedJet A (g+g') b P j⟩,
      P,hPI,hP,b,j,rfl⟩,fun x hx => hx,?_⟩
    intro x hx
    exact normalizedJet_composition_finite A g g' x b P hx u v
  · apply locallyGeneratedIdeal_le_of_section_replacements
    rintro ⟨f,P,hPI,hP,b,j,rfl⟩
    let w := List.ofFn j.directions
    let u := w.take T
    let v := w.drop T
    have hu : u.length ≤ T := List.length_take_le _ _
    have hv : v.length ≤ T' := by
      dsimp [v,w]
      rw [List.length_drop,List.length_ofFn]
      have hj := j.order_le
      omega
    let s : LocalSection G :=
      ⟨{x | g+g'+x ∈ chartDomain G b}, fun x =>
        iteratedFDeriv K u.length
          (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
            normalizedJet A g' b P
              (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
              (g + x + A.map ⟨z,hz⟩) else 0) 0
            (fun i => Pi.single (u.get i) 1)⟩
    refine ⟨⟨s,P,hPI,hP,b,u,hu,v,hv,rfl⟩,fun x hx => hx,?_⟩
    intro x hx
    change normalizedJet A (g+g') b P j x = _
    dsimp only [s]
    have hw : normalizedJet A (g+g') b P
        (⟨w.length,le_rfl,w.get⟩ : JetIndex A.parameterDimension w.length) x =
        normalizedJet A (g+g') b P j x := by
      unfold normalizedJet
      apply JetSupport.iteratedFDeriv_apply_congr (List.length_ofFn (f := j.directions))
      intro i
      simp only [w,List.get_ofFn]
    have hs := congrArg
      (fun a : List (Fin A.parameterDimension) => normalizedJet A (g+g') b P
        (⟨a.length,le_rfl,a.get⟩ : JetIndex A.parameterDimension a.length) x)
      (List.take_append_drop T w)
    exact hw.symm.trans (hs.symm.trans (normalizedJet_composition_finite A g g' x b P hx u v).symm)

end PhilipponMultiplicity.OperatorSupport

end

theorem solution
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g g' : G.Point) (T T' : ℕ) (I : Ideal G.CoordinateRing) :
    locallyGeneratedIdeal G (iteratedDifferentialSections A g g' T T' I) =
      differentialIdeal A (g+g') (T+T') I := by
  exact OperatorSupport.iterated_jet_sections_eq_differentialIdeal A g g' T T' I
