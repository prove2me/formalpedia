-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_spherical_scalar_producer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:31:11.340728+00:00
-- url     : https://prove2.me/submissions/4176c6a9-6d6b-4a5d-b25d-15ef4a1410de

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_eventually_scalar_factor_raw
import Theorems.Thm_OAI_YauCounterexamples_exists_spherical_global_quasimodes
import Theorems.Thm_OAI_YauCounterexamples_nonempty_compactMetricAtlas

section
-- module Solutions.OAIQ070_YAU.Compat
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ManifoldChartPush
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma manifoldChartPush_apply (p : M) (f : E → V) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    manifoldChartPush p f ((chartAt E p).symm y) = f y := by
  simp only [manifoldChartPush, Set.indicator_of_mem ((chartAt E p).map_target hy),
    Function.comp_apply, (chartAt E p).right_inv hy]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPower_smooth (a b : Euclidean (d+1)) (k : ℕ) :
    ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ (roundPower a b k) := by
  have hc : ContDiff ℝ ∞ (fun x : Euclidean (d+1) => (planarLinear a b x)^k) :=
    (planarLinear a b).contDiff.pow k
  exact (Complex.reCLM.contDiff.comp hc).contMDiff.comp contMDiff_coe_sphere


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeCoupledCleanChartJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter Manifold
open scoped Topology ContDiff

lemma sphericalWaveLift_apply (u : Euclidean 3 → ℝ) (y : Euclidean 3) :
    sphericalWaveLift u ((chartAt (Euclidean 3) sourcePole).symm y)=u y :=
  manifoldChartPush_apply sourcePole u (by rw [sphere_chart_target]; trivial)

lemma sphericalWaveLift_smooth {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (sphericalWaveLift u) :=
  contMDiff_manifoldChartPush sourcePole hu hc (by rw [sphere_chart_target]; exact subset_univ _)


end


section
open Set Filter Manifold
open scoped Topology ContDiff

lemma sphericalWeight_pos (φ : Sphere 3 → ℝ) (n : ℕ) (q : Sphere 3) :
    0 < sphericalWeight φ n q := add_pos_of_pos_of_nonneg (Real.exp_pos _) (by positivity)

end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ExistsSphericalScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace YauCounterexamples
open Filter

lemma eventual_choice_with_good_default {α β : Type*} {l : Filter α}
    (Q : β → Prop) (b : β) (hb : Q b) (P : α → β → Prop)
    (h : ∀ᶠ a in l, ∃ u, Q u ∧ P a u) :
    ∃ u : α → β, (∀ a, Q (u a)) ∧ ∀ᶠ a in l, P a (u a) := by
  classical
  let good (a : α) := ∃ u, Q u ∧ P a u
  let u : α → β := fun a => if ha : good a then ha.choose else b
  refine ⟨u,fun a => ?_,?_⟩
  · by_cases ha : good a
    · simpa only [u,dite_eq_left ha] using ha.choose_spec.1
    · simpa only [u,dite_eq_right ha] using hb
  · filter_upwards [h] with a ha
    change good a at ha
    simpa only [u,dite_eq_left ha] using ha.choose_spec.2
end YauCounterexamples


noncomputable section
open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples

theorem exists_spherical_scalar_producer_oai
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r) (hr : r < 3/10)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hFt : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q < t)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) :
    ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
    ∀ (tests : List (CoordinateTest (Euclidean 3) (Sphere 3))) (N P : ℕ),
      ∃ L > 0, ∀ᶠ n : ℕ in atTop,
      ∃ u : Euclidean 3 → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
        tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
          ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
      let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
      let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) U
      let z := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) U
      (∀ x, U x=0 → 0 < coordinateGradientPair g U U x) ∧
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ b ∧
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ z ∧
      (∀ x, 0 < b x ∧ 0 < z x) ∧
      (∀ x, weightedLaplacian g b U x+sphereFrequency n*z x*U x=0) ∧
      tsupport (fun x => b x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+sphereFrequency n*U x) ∧
      tsupport (fun x => z x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+sphereFrequency n*U x) ∧
      ∃ v : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
        (∀ x, weightedLaplacian g b v x = sphereFrequency n*b x^3*v x^5-sphereFrequency n*z x*v x) ∧
        (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
          |z x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
        (∀ a ∈ tests, ∀ y ∈ a.compactSet, ∀ j ≤ N,
          ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => z x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P) ∧
        ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
          (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
          (fun a => ε/((n:ℝ)*ℓ a.val))
          ((U ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) := by
  classical
  obtain ⟨φ,hφ,hin,hout,partition,hpart,ℓ,hℓ,ε,hε,hproduce⟩ :=
    exists_spherical_global_quasimodes g₀ hg₀ g hg ht hts hsr hr hF hFt hext hmetric A
  refine ⟨partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  intro tests N P
  let k := N+2
  have hs : Module.finrank ℝ (Euclidean 3) < 2*(2*(k:ℝ)) := by
    simp only [Euclidean,finrank_euclideanSpace,Fintype.card_fin,k,Nat.cast_add,Nat.cast_ofNat]
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  let atlas := Classical.choice (nonempty_compactMetricAtlas g k hs)
  let D := (P+8)+((2*110+21)*(2*(k+1)+2)+10)+2
  obtain ⟨C,hC,hpacket⟩ := hproduce atlas.t atlas.p atlas.scalarChartSupport
    atlas.scalarChartSupport_compact (2*(k+1)+2) D
  let good (u : Euclidean 3 → ℝ) := ContDiff ℝ ∞ u ∧ HasCompactSupport u
  have hzero : good 0 := ⟨contDiff_const,by simpa using (HasCompactSupport.zero : HasCompactSupport (0 : Euclidean 3 → ℝ))⟩
  obtain ⟨u,hu,hpacket⟩ := eventual_choice_with_good_default good 0 hzero
    (fun n u => tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
      (∀ q : Sphere 3, sphericalWeight φ n q/(n:ℝ)^110 ≤
        |(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q|+
        Real.sqrt (coordinateGradientPair g
          (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u)
          (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q)/(n:ℝ)) ∧
      (∀ i : atlas.t, ∀ y ∈ atlas.scalarChartSupport i, ∀ j ≤ 2*(k+1)+2,
        ‖iteratedFDeriv ℝ j ((roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) ∘
          (chartAt (Euclidean 3) (atlas.p i)).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*sphericalWeight φ n ((chartAt (Euclidean 3) (atlas.p i)).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
          (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
          sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ∘
          (chartAt (Euclidean 3) (atlas.p i)).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*sphericalWeight φ n ((chartAt (Euclidean 3) (atlas.p i)).symm y)) ∧
      ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
        (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
        (fun a => ε/((n:ℝ)*ℓ a.val))
        (((roundPower sourceAxisOne sourceAxisTwo n ∘
          (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv))
    (hpacket.mono (by
      rintro n ⟨u,hu,hc,hs,hlow,hj,hscore,_⟩
      exact ⟨u,⟨hu,hc⟩,hs,hlow,hj,hscore⟩))
  let U (n : ℕ) := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift (u n)
  have hU (n : ℕ) : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (U n) :=
    (roundPower_smooth _ _ _).add (sphericalWaveLift_smooth (hu n).1 (hu n).2)
  have hNP : N ≤ 2*(k+1) := by dsimp [k]; omega
  have hN : Module.finrank ℝ (Euclidean 3) < 2*(2*((k+1:ℕ):ℝ)-N) := by
    simp only [Euclidean,finrank_euclideanSpace,Fintype.card_fin,k,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  obtain ⟨L,hL,hfactor⟩ := atlas.eventually_scalar_factor_raw (by simp [Euclidean]) tests
    N P 110 D hNP hN (by exact le_rfl) hC U (sphericalWeight φ) hU (sphericalWeight_pos φ)
    (hpacket.mono (fun n hn => ⟨hn.2.1,
      fun i y hy j hj => (hn.2.2.1 i y hy j hj).1,
      fun i y hy j hj => (hn.2.2.1 i y hy j (by omega)).2⟩))
  refine ⟨L,hL,?_⟩
  filter_upwards [hpacket,hfactor,eventually_ge_atTop (1:ℕ)] with n hp hf hn
  obtain ⟨hb,hz,hpos,heq,hbs,hzs,v,hv,hvp,hve,hsmall,hraw⟩ := hf
  have hreg (x : Sphere 3) (hx : U n x=0) : 0 < coordinateGradientPair g (U n) (U n) x := by
    have hlow := hp.2.1 x
    change sphericalWeight φ n x/(n:ℝ)^110 ≤ |U n x|+_ at hlow
    rw [hx,abs_zero,zero_add] at hlow
    have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hsqrt : 0 < Real.sqrt (coordinateGradientPair g (U n) (U n) x) := by
      have hdiv := (div_pos (sphericalWeight_pos φ n x) (pow_pos hnpos 110)).trans_le hlow
      exact (div_pos_iff_of_pos_right hnpos).mp hdiv
    exact Real.sqrt_pos.mp hsqrt
  refine ⟨u n,(hu n).1,(hu n).2,hp.1,hreg,hb,hz,hpos,heq,hbs,hzs,v,hv,hvp,hve,hsmall,hraw,?_⟩
  have he : ((U n ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv)=
      (((roundPower sourceAxisOne sourceAxisTwo n ∘
        (chartAt (Euclidean 3) sourcePole).symm)+u n) ∘ normalWaveEquiv) := by
    funext x
    simp only [U,Function.comp_apply,Pi.add_apply,sphericalWaveLift_apply]
  rw [he]
  exact hp.2.2.2

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_spherical_scalar_producer_oai := @OAI.YauCounterexamples.exists_spherical_scalar_producer_oai
