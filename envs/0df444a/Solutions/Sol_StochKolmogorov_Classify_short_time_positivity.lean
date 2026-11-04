-- Prove2me | solution 1 for StochKolmogorov.Classify.short_time_positivity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T09:31:58.328882+00:00
-- url     : https://prove2.me/submissions/9edab49b-0aee-4138-b824-29bd784e027b

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Theorems.Thm_EthierKurtz_brownian_ito_integral_and_formula
import Theorems.Thm_EthierKurtz_brownian_ito_integral_locality_and_continuity
import Theorems.Thm_StochKolmogorov_Persist_orthant_invariance_closed
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2
import Theorems.Thm_EthierKurtz_brownian_ito_doob_maximal

set_option linter.all false
set_option Elab.async false


-- ===== Shift =====
section FlatM_Shift

/-! Path-shift invariance of the sink event (deterministic part of K4b): if the path `ω'` of `X'`
from `x'` is the path `ω` of `X` from `x` shifted by `t`, then `ω' ∈ extinctEvent C X' x' μ ↔
ω ∈ extinctEvent C X x μ`. The occupation measures differ by `O(t/T)`, the log rates by a factor
`(t+s)/s → 1`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.Shift

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.Shift

end FlatM_Shift
-- ===== K3 =====
section FlatM_K3

/-! K3 of theorem_1_3 (8f909832): each sink event is null-measurable, GIVEN the a.e. cover (K2) and
injectivity of `supp` on the measures (K1b). Idea: `E_μ ⊆ A_μ := Z_μ ∩ L_μ` with `A_μ` measurable, where
`Z_μ` = "the Cesaro means of `min 1 |X_i|` along integers tend to 0 for `i ∉ supp μ`" and
`L_μ` = "they have positive limsup for `i ∈ supp μ`" (both read at RATIONAL times, so `A_μ` is the preimage of a measurable path set `Gam`). `A_μ ∩ E_ν = ∅` for `ν ≠ μ` (it forces
`supp μ = supp ν`), so `A_μ \ E_μ` lies in the null set where the cover fails. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.K3

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- truncated coordinate size `min 1 |y_i|` -/
noncomputable def g (i : Fin n) (y : SDEState n) : ℝ := min 1 |y i|

end StochKolmogorov.Classify.K3

end FlatM_K3
-- ===== PathMix =====
section FlatM_PathMix

/-! PM2b of K4b (8f909832): a mixture identity `P(Y ∈ Γ) = ∫ P(Z y ∈ Γ) dκ(y)` (with measurable
`y ↦ P(Z y ∈ Γ)`) that holds on measurable cylinders of the path space `ι → E` holds on every
set of the product σ-algebra (Dynkin's π-λ theorem). Used with `ι = ℚ`, `Y` = the time-`t`-shifted
rational path of `X x`, `Z y` = the rational path of `X y`, `κ = trans P X t x`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.PathMix

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

end StochKolmogorov.Classify.PathMix

end FlatM_PathMix
-- ===== K4 =====
section FlatM_K4

/-! K4 of theorem_1_3 (8f909832): every sink has positive probability from every interior point, from
* `hinj` (K1b), `hcover` (K2), `h59` (sibling lemma_5_9), `hreach` (K4a irreducibility),
* `hFD` (PM1: finite-dimensional Markov identity for the rational path after time `t`).
Route: `E_x =ᵐ {shifted rational path ∈ Gam}` (K3 + path-shift invariance), the mixture identity on
the path σ-algebra (PathMix), and `P(E_y) ≥ 1/2` on an open box inside `Kbox μ 2 Δ`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.K4

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.K4

end FlatM_K4
-- ===== FDM =====
section FlatM_FDM

/-! PM1 glue of K4b (8f909832): `K4.FDMarkov` (finite-dimensional Markov identity of the rational
path after time `t`, for Lipschitz test functions bounded by 1) from the child theorem
`EthierKurtz.sde_markov_property_fd_conditional` (case q = 0), applied to Lipschitz truncations of the Kolmogorov
coefficients (copied from the accepted `Persist.markov_property` reduction, namespace renamed). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDM

open StochKolmogorov.Classify EthierKurtz

variable {d : ℕ}
/-- Coordinatewise 1-Lipschitz maps are 1-Lipschitz in the Euclidean norm. -/
theorem norm_sub_le_of_coord {x y x' y' : SDEState d} (h : ∀ i, |x' i - y' i| ≤ |x i - y i|) :
    ‖x' - y'‖ ≤ ‖x - y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

variable {n : ℕ}

theorem posPart_apply' (x : SDEState n) (i : Fin n) : posPart x i = max (x i) 0 := rfl

theorem posPart_lip (x y : SDEState n) : ‖posPart x - posPart y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by
    rw [posPart_apply', posPart_apply']; exact abs_max_sub_max_le_abs _ _ _

theorem continuous_posPart : Continuous (posPart (n := n)) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]; exact posPart_lip x y)

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

variable {n : ℕ}

end StochKolmogorov.Classify.FDM

end FlatM_FDM
-- ===== FDMC =====
section FlatM_FDMC

/-! K2-mc step 1 (8f909832): conditional finite-dimensional Markov identity, tested against a
Lipschitz functional `G` of finitely many past rational times in `(0, t]`, from child C
(`EthierKurtz.sde_markov_property_fd_conditional`) with `q = s'.card`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDMC

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.FDMC

end FlatM_FDMC
-- ===== PathMix2 =====
section FlatM_PathMix2

/-! K2-mc (8f909832): two-measure version of PathMix. `Q` (finite; e.g. `P` weighted by a past
functional) governs `Y`, the probability `P` governs `Z y`, and `κ` (finite, same mass as `Q`)
mixes: `Q(Y ∈ Γ) = ∫ P(Z y ∈ Γ) dκ(y)`. Used for the conditional (past-weighted) path Markov
identity: `Q = P.withDensity (G ∘ past)`, `κ = Q.map (X x s)`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.PathMix2

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

end StochKolmogorov.Classify.PathMix2

end FlatM_PathMix2
-- ===== CondMix =====
section FlatM_CondMix

/-! K2-mc steps 2-3 (8f909832), generic: from the conditional finite-dimensional Markov identity
(Lipschitz tests `G` of the past path `V`, `F` of the future path `Y`) to the conditional path
identity `P(Y ∈ Γ, V ∈ A) = ∫_{V ∈ A} P(Z (Xt ω) ∈ Γ) dP(ω)` for all measurable `A`, `Γ`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.CondMix

variable {Ω E ι ι' : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

end StochKolmogorov.Classify.CondMix

end FlatM_CondMix
-- ===== FDMC2 =====
section FlatM_FDMC2

/-! K2-mc (8f909832): the conditional path Markov identity for the Kolmogorov solution family:
`P(shiftPath_t ∈ Γ, past_t ∈ A) = ∫_{past_t ∈ A} P(Zf (X x t ω) ∈ Γ) dP(ω)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDMC

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.FDMC

end FlatM_FDMC2
-- ===== T1a =====
section FlatM_T1a

/-! T1a `grid_escape_bound` (a17b7893 s4): Hening-Nguyen 1704.06984 (5.29)-(5.30).
`Ũ(X(j T₀))` is a supermartingale along the grid (one step = Extinct.one_step_5_11_5_12 over
proposition_5_1, lemma_5_2, inequalities_5_1_5_2), so the kernel Doob inequality
`P(∃ j, Ũ(X(j T₀)) ≥ a) ≤ Ũ(x)/a` (induction on the horizon over the path Markov identity
`FDMC.condPath_of`) bounds the escape probability; `Ũ < a ≤ ς` forces `xᵢ < β` off `supp μ`. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace StochKolmogorov.Classify.GE
open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

theorem exists_isDelta0 (C : Coeffs n) (γb : ℝ) (hγ : 0 < γb) :
    ∃ δ₀ : ℝ, IsDelta0 C γb δ₀ := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsij : ∀ i j, |C.sig i j| ≤ S := by
    intro i j
    calc |C.sig i j| ≤ ∑ j', |C.sig i j'| :=
          Finset.single_le_sum (f := fun j' => |C.sig i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C.sig i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hden : 0 < 3 * S * n + 3 := by positivity
  refine ⟨γb / (3 * S * n + 3), div_pos hγ hden, ?_, fun x _ => ?_⟩
  · rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [mul_nonneg hS0 (Nat.cast_nonneg (α := ℝ) n)]
  · set δ := γb / (3 * S * n + 3) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hγ hden).le
    set G : ℝ := ∑ i, C.g i x ^ 2 with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, |C.g i x * C.g j x * C.sig i j|
        ≤ S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |C.g i x| * |C.g j x| ≤ (C.g i x ^ 2 + C.g j x ^ 2) / 2 := by
        nlinarith [sq_nonneg (|C.g i x| - |C.g j x|), sq_abs (C.g i x), sq_abs (C.g j x)]
      calc |C.g i x| * |C.g j x| * |C.sig i j| ≤ ((C.g i x ^ 2 + C.g j x ^ 2) / 2) * S :=
            mul_le_mul h1 (hsij i j) (abs_nonneg _) (by positivity)
        _ = S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by ring
    have hsum : ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| ≤ S * n * G := by
      calc ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
          ≤ ∑ i : Fin n, ∑ j : Fin n, S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = S * n * G := by
            simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hG, ← Finset.sum_div]
            ring
    have hkey : δ * (3 * S * n + 3) = γb := by rw [hδ, div_mul_cancel₀ _ hden.ne']
    calc 3 * δ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ * G
        ≤ 3 * δ * (S * n * G) + δ * G := by nlinarith
      _ ≤ δ * (3 * S * n + 3) * G := by nlinarith [mul_nonneg hδ0 hG0]
      _ = γb * G := by rw [hkey]

/-! ### Deterministic facts about `Ũ` -/

/-! ### Kernel Doob inequality along the grid -/

end StochKolmogorov.Classify.GE

end FlatM_T1a
-- ===== T1 =====
section FlatM_T1

/-! T1 `sink_box_avoids_far_set` glue (a17b7893 s4): Hening-Nguyen 1704.06984 (5.27)-(5.33).
First dyadic hitting time of the far set `O(R,η)`, the path Markov identity `FDMC.condPath_of`
and short-time positivity (T1b) give `P(hit O on grid m) ≤ 2 P(some grid value jT₀ has Xᵢ ≥ β)`;
continuity and openness of `O` pass to all times, and T1a bounds the right side. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace StochKolmogorov.Classify.SB
open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

end StochKolmogorov.Classify.SB

end FlatM_T1
-- ===== ItoM1 =====
section FlatM_ItoM1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

end BM

section AEC
variable {mΩ : MeasurableSpace Ω}

end AEC

section CP
variable [MeasurableSpace Ω]

end CP

section M2

variable [MeasurableSpace Ω]

end M2

section M3
variable [MeasurableSpace Ω]

end M3

section M4
variable [MeasurableSpace Ω]

end M4


section StopCoef

end StopCoef

section M5
variable [MeasurableSpace Ω]

end M5


section M5b

end M5b

section M5c
variable [MeasurableSpace Ω]

end M5c


section M6refine

end M6refine


section M6osc

/-- The dyadic time `j t / 2^N`. -/
noncomputable def dyTime (t : ℝ≥0) (N j : ℕ) : ℝ≥0 := (j : ℝ≥0) * t / (2 : ℝ≥0) ^ N

theorem dyTime_le (t : ℝ≥0) {N j : ℕ} (h : j ≤ 2 ^ N) : dyTime t N j ≤ t := by
  unfold dyTime
  rw [div_le_iff₀ (by positivity)]
  calc (j : ℝ≥0) * t ≤ (2 : ℝ≥0) ^ N * t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h) zero_le
    _ = t * 2 ^ N := mul_comm _ _

end M6osc


section M6cauchy
variable [MeasurableSpace Ω]

end M6cauchy


section M6limit
variable [MeasurableSpace Ω]

end M6limit


section M6trunc

end M6trunc

section M6exist
variable [MeasurableSpace Ω]

end M6exist


section M7grid

end M7grid

section M7zero
variable [MeasurableSpace Ω]

end M7zero


section M7qv
variable [MeasurableSpace Ω]

end M7qv

section M7c
variable [MeasurableSpace Ω]

end M7c

section M8a
variable [MeasurableSpace Ω]

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

/-- Locality of the Ito integral: integrands agreeing on the dyadic grid of `[0, s]` on an event
give integrals agreeing a.e. on that event at time `s`. -/
theorem hasBrownianItoIntegral_eq_on {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H H' J J' : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hH'm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H' s))
    (hH'c : ∀ ω, Continuous fun s => H' s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ' : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H' J') (s : ℝ≥0) (E : Set Ω)
    (hE : ∀ ω ∈ E, ∀ N i : ℕ, i ≤ 2 ^ N → H (dyTime s N i) ω = H' (dyTime s N i) ω) :
    ∀ᵐ ω ∂P, ω ∈ E → J s ω = J' s ω := by
  exact (EthierKurtz.brownian_ito_integral_locality_and_continuity hW x₀).1 j H H' J J' hHm hHc hH'm hH'c hJ hJ' s E hE

end M8c

section M8d
variable [MeasurableSpace Ω]

end M8d

section M8e
variable [MeasurableSpace Ω]

end M8e


section M8f
variable [MeasurableSpace Ω]

end M8f


section M8f2
variable [MeasurableSpace Ω]

end M8f2


section M8f3
variable [MeasurableSpace Ω]

end M8f3


section M8gTaylor
open Set

end M8gTaylor

section M8g
variable [MeasurableSpace Ω]

end M8g


section M8g2

end M8g2


section M8g3
variable [MeasurableSpace Ω]

end M8g3

section M8g4
variable [MeasurableSpace Ω]

end M8g4

section M8g5
variable [MeasurableSpace Ω]

end M8g5

section M9a
variable [MeasurableSpace Ω]

end M9a


section M9c
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

end M9cF


section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

end M9d


section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

end M9d2



section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

end M9e1


section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2


end ItoLib

end FlatM_ItoM1
-- ===== E =====
section FlatM_E
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10b1
/-! M10b-1: pathwise identification of Ito integrals. For an integrand that is an indefinite
integral in time (`h s = h 0 + ∫₀ˢ D`), left-point sums converge pathwise to the integration by
parts value `h t w t - h 0 w 0 - ∫₀ᵗ w D`; and pathwise limits of left-point sums are Ito
integrals in the sense of `HasBrownianItoIntegral`. -/

end M10b1

section M10b2
/-! M10b-2 (generic part): piecewise-linear interpolation of a sequence on the grid `k h`,
defined as a primitive of the piecewise-constant slope. -/

end M10b2

section M10b2s
/-! M10b-2: the truncated Euler scheme with lagged, linearly interpolated coefficients, driven by a
deterministic path `w`. `eulerZZ k = (Z_{k-1}, Z_k)`. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)
  (w : ℝ≥0 → SDEState d)

variable {s₁ b₁ h w}

end M10b2s


section M10b2w
/-! M10b-2 (random part): the scheme driven by a Brownian path is adapted, continuous, and an
Ito process. Measurability is proved for any monotone family `G` of σ-algebras that sees the
past of `W` (used with `G = completedBrownianPast` and with the ambient σ-algebra). -/

variable {W : ℝ≥0 → Ω → SDEState d} {G : ℝ≥0 → MeasurableSpace Ω}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2w


section M10b2i
/-! M10b-2: the scheme driven by standard Brownian motion is an Ito process in the sense of
`ito_formula`. -/

variable [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2i


section M10b4a
/-! M10b-4 (a): Ito formula for `Ff r` along `(X, Y, A)` where `X`, `Y` are general Ito
processes (matrix integrands `HX`, `HY`, drifts `bX`, `bY`), `A = ∫ κ(X, Y)`. -/

end M10b4a


section M10b4b
/-! M10b-4 (b): pathwise bounds for the generator `driftG` when `X` has coefficients
`σ₀(X), b₀(X)` and `Y` has arbitrary coefficients `σy, by'`. -/

end M10b4b

end ItoLib

end FlatM_E
-- ===== F =====
section FlatM_F
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c1
/-! M10c-1: the saturating profile `ψ(Q) = 1 - (1 - st(Q/4)) e^{-Q}` (`ψ(0) = 0`, `ψ = 1` for
`Q ≥ 4`, `ψ(Q) ≥ Q/5` on `[0,4]`) and the test function
`Gf r (x, y, a) = e^{-a} χ_r(|x|²) ψ(|x-y|²)` (cut-off in `x` only). -/

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

end M10c2

section M10c3
/-! M10c-3: pointwise bounds for the generator `driftH` of `Gf r`. -/

end M10c3

end ItoLib

end FlatM_F
-- ===== G =====
section FlatM_G
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c4
/-! M10c-4: the Ito formula along `(X, Y, A)` for an arbitrary `C²` test function `F` whose
martingale integrands are bounded (`ito_coupled_F`); applied to `Gf r`. -/

end M10c4


section M10c5
/-! M10c-5: expectation bound for `Gf r` along `(X, Y, A)`, `X` the SDE solution, `Y` a general
Ito process with globally bounded coefficients, clock rate `kapX` (penalising only `X`). -/

end M10c5


section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c6

end ItoLib

end FlatM_G
-- ===== H =====
section FlatM_H
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c7
/-! M10c-7: the Euler scheme's coefficient error `‖s₁(Y_u) - H_u‖`, `‖b₁(Y_u) - b_u‖` is
`≤ 2 L K` with `K = d (3 d S δ + 2 S h)` (`δ` = oscillation of `w` over gaps `≤ h` on `[0, T]`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c7

section M10c8
/-! M10c-8: the coupled expectation bound `lintegral_Gf_le` with `Y` the truncated Euler scheme
driven by `W` (lag start `a = y = x₀`), `s₁ = σ₀`, `b₁ = b₀` on `B̄_{R+3}`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10c8

section M10c9
/-! M10c-9: `E ∫₀ᵗ eulerErr → 0` along any mesh sequence `hₙ → 0` (globally Lipschitz,
bounded truncated coefficients). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c9

section M10c10
/-! M10c-10: the truncated Euler scheme converges to the SDE solution in probability on the
event that `X` stays in `B̄_R` (truncation radius `≥ R + 3`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c10

end ItoLib

end FlatM_H
-- ===== I =====
section FlatM_I
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d1
/-! M10d-1 (b5 groundwork): the cell noise `ζ_j = (1/h) ∫₀ʰ (W(s+h) - W(s+u)) du`: measurable for
the future-increment σ-algebra (so independent of the completed past), mean zero, `E ζ² ≤ h/2`. -/

end M10d1

section M10d2
/-! M10d-2: one cell of the L² stability estimate: for completed-past-measurable `D` (L²) and
bounded `A, B`, `E‖D + N‖² ≤ E‖D‖² + 2 d h E(‖A‖² + ‖B‖²)` with the cell noise
`N_i = Σⱼ (A_ij ξ_j + B_ij ζ_j)`. -/

end M10d2

end ItoLib

end FlatM_I
-- ===== J =====
section FlatM_J
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d3
/-! M10d-3 (b5): one full cell of the Euler scheme in cell-noise form, and L² of the grid values. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10d3

end ItoLib

end FlatM_J
-- ===== K =====
section FlatM_K
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e1
/-! M10e-1 (b6 groundwork): the scheme as a deterministic recursion `zrec` driven by the cell
noises `(ξ_l, ζ_l)`; restart identity `Z_{m+k} = zrec_k(Z_{m-1}, Z_m; noises of cells m, m+1, ...)`;
the noises after cell `m` are measurable for the future-increment σ-algebra. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable {s₁ b₁ h}

end M10e1

section M10e2
/-! M10e-2 (b6): restart at a grid time. Independence of the past pair `(Z_{m-1}, Z_m)` and the
future noises gives `E f(Z_{m+k}) = E[ E' f(zrec_k(Z_{m-1}, Z_m; noises after m)) ]`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e2

end ItoLib

end FlatM_K
-- ===== L =====
section FlatM_L
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e3
/-! M10e-3 (b6): time homogeneity. The restarted Brownian motion is standard; the noises after
cell `m` are the noises of the restarted motion; any two standard Brownian motions have the same
finite-dimensional laws. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10e3

section M10e4
/-! M10e-4 (b6 DONE): restart in law at a grid time: `E f(Z_{m+k}) = E G(Z_{m-1}, Z_m)` with
`G(a, y) = E f(Z_k from (a, y))`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e4

end ItoLib

end FlatM_L
-- ===== CB =====
section FlatM_CB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CB (CORE route C2, s22): Cameron-Martin shift formula for centered Gaussians, one-dimensional
and for finite independent families (`Measure.pi`). -/

end ItoLib

end FlatM_CB
-- ===== CC =====
section FlatM_CC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C2b
/-! CORE route C2b (s23): one-cell Cameron-Martin for the cell noise `(ξ, ζ)` with a constant shift:
weighting by `cmwPi h u ξ` and shifting `(ξ, ζ) ↦ (ξ + u, ζ + u/2)` preserves the law.
Route: dyadic increments are i.i.d. `N(0, h/2^n)` (`dInc_law`), the dyadic approximation of the
noise is a linear function `psiN` of them (`apx_eq_psiN`), finite-dimensional Cameron-Martin
(`gauss_pi_shift`) at each level, then the limit `n → ∞`. -/

end C2b

end ItoLib

end FlatM_CC
-- ===== CD =====
section FlatM_CD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C3
/-! CORE route C3 (s23): adapted discrete Girsanov over the cells. The first `k` cell noises have
law `ν_k = ν_{k-1} ⊗ ν_1` (independence of the past and time homogeneity); shifting cell `l` by
`(u_l, u_l/2)` with `u_l` a measurable function of the earlier noises and weighting by
`∏ cmwPi h u_l ξ_l` preserves `ν_k` (`girsanov_cells`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end C3

end ItoLib

end FlatM_CD
-- ===== CE =====
section FlatM_CE
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {d : ℕ}

section C4a
/-! CORE route C4a (s23): the steered coupling, deterministic part. Two copies of the scheme are run
on one noise sequence; the second copy uses the shifted noise `n + (u, u/2)` with the adapted
steering `u_l = J(Ŷ pair)((X_l - Ŷ_l)/(m - l))`. The shift adds `avgApply p u` to a step
(`zstep_shift`), so with a right inverse `J` of `avgApply` the step adds `(X_l - Ŷ_l)/(m - l)`
(`cstep_steer`). The steered copy is the plain scheme driven by `shV (steerN ..)` (`shV_crec`). -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)

variable {s₁ b₁ h J m}

end C4a

end ItoLib

end FlatM_CE
-- ===== CF =====
section FlatM_CF
open Filter Set
open scoped BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CORE route C4b (s23): the steered second-moment recursion. If
`e_{k+1} ≤ (1 - 1/(m-k))² e_k + c h (e_k + e_{k-1})` (with `e_{-1}` given by `e' 0`), then
`e_k ≤ G ((m-k)/m)² (1 + 13 c h)^k` for `k < m`. Key fact: `(j+1)² + (j+2)² ≤ 13 j²` for `j ≥ 1`. -/

end ItoLib

end FlatM_CF
-- ===== CG =====
section FlatM_CG
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C4c
/-! CORE route C4c (s24): the steered coupling driven by a Brownian motion. Past-measurability of
the coupled chain, the one-step identity `D_{k+1} = (1 - 1/(m-k)) D_k + h/2 Δb + cellNoise`,
and the second-moment step feeding `steer_rec` (CF.lean). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4c

end ItoLib

end FlatM_CG
-- ===== CH =====
section FlatM_CH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
variable {Ω : Type*}

section C4d
/-! CORE route C4d (s24): lower bound of a weighted event by the relative entropy, with no second
moment of the Girsanov martingale. If `f > 0`, `E f ≤ 1` and `E[-log f] ≤ K`, then
`E[1_E f] ≥ e^{-a} (P E - (K+1)/a)` (Markov on `-log f + f ≥ (-log f)⁺`). -/

end C4d

section C4d2
/-! C4d (s25): the relative entropy of the steering weight. -/
open EthierKurtz

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4d2

end ItoLib

end FlatM_CH
-- ===== CI =====
section FlatM_CI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
set_option autoImplicit false

namespace ItoLib

section C5a
/-! CORE route C5a (s25): Kolmogorov's maximal inequality in the abstract form needed for the
exit estimate of the Euler chain. The only probabilistic input is the orthogonality of the
"stopped" value `1_{F_k} M_k` to the remaining increment `M_m - M_k`. -/

variable {Ω : Type*} {d : ℕ}

end C5a

end ItoLib

end FlatM_CI
-- ===== CK =====
section FlatM_CK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5c
/-! CORE route C5c (s26): exit estimate for the Euler chain with bounded coefficients.
`Z_k = Z_0 + M_k + D_k` with `M` the martingale part (orthogonal cell increments) and `D` the
drift part (`‖D_k‖ ≤ k h S`); Kolmogorov's maximal inequality on `M` gives
`(δ/2)^2 P(∃ k ≤ m, ‖Z_k - Z_0‖ ≥ δ) ≤ 16 d S^2 m h` once `m h S ≤ δ/2`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end C5c
end ItoLib

end FlatM_CK
-- ===== CL =====
section FlatM_CL
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5d
/-! CORE route C5d (s26): a global, measurable, bounded right inverse of `avgApply` for diffusions
of the form `s x (i, j) = a i x * Γ j i` (the Kolmogorov diffusion read through a projection),
when `Γ` is invertible and `|a i x + a i y| ≥ κ > 0`. -/

variable {d : ℕ}

end C5d
end ItoLib

end FlatM_CL
-- ===== M =====
section FlatM_M
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f1
/-! M10f-1 (b7 groundwork): the restart function `G_k(a, y) = E f(Z_k from (a, y))` is Lipschitz
in the initial pair for Lipschitz `f`, uniformly in the mesh (via `euler_stab_exp`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f1

end ItoLib

end FlatM_M
-- ===== N =====
section FlatM_N
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f2
/-! M10f-2 (b7): uniform smallness of Euler cell increments, and the exit probability
`P(path leaves B̄_R before T) → 0`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {w : ℝ≥0 → SDEState d}

variable [MeasurableSpace Ω]

end M10f2

section M10f3
/-! M10f-3 (b7): the Euler scheme approximates `X_T` in law, up to the exit probability. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f3

section M10f4
/-! M10f-4 (b7): the real-analysis wrap-up of the Chapman-Kolmogorov limit
(reverse Fatou in `n`, dominated convergence in `R`). -/

variable [MeasurableSpace Ω]

end M10f4

section M10f5
/-! M10f-5 (b7): the restart function `eulerG`, its bound and uniform Lipschitz property, and the
approximation `eulerG(y, y) ≈ E f(X^y_t)` up to the exit probability. -/

variable [MeasurableSpace Ω]

variable {P : Measure Ω} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f5

section M10f6
/-! M10f-6 (b7 DONE): Chapman-Kolmogorov in integrated form for bounded Lipschitz test functions,
with a measurable version `g` of `y ↦ E f(X^y_t)`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f6

end ItoLib

end FlatM_N
-- ===== O =====
section FlatM_O
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10g
/-! M10g: from integrated Chapman-Kolmogorov identities for thickened indicators (bounded
Lipschitz test functions) to a Markov kernel and set-wise Chapman-Kolmogorov. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10g

end ItoLib

end FlatM_O
-- ===== P =====
section FlatM_P
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10h
/-! M10h (b9/b11): local Lipschitz on compact sets, coordinate clamps, truncation families,
and the Kolmogorov coefficients. -/

variable {d : ℕ}

/-- Coordinatewise 1-Lipschitz maps are 1-Lipschitz in the Euclidean norm. -/
theorem norm_sub_le_of_coord {x y x' y' : SDEState d} (h : ∀ i, |x' i - y' i| ≤ |x i - y i|) :
    ‖x' - y'‖ ≤ ‖x - y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

end M10h

section M10i
open StochKolmogorov.Persist
variable {n : ℕ}

theorem posPart_apply' (x : SDEState n) (i : Fin n) : posPart x i = max (x i) 0 := rfl

theorem posPart_lip (x y : SDEState n) : ‖posPart x - posPart y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by
    rw [posPart_apply', posPart_apply']; exact abs_max_sub_max_le_abs _ _ _

theorem continuous_posPart : Continuous (posPart (n := n)) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]; exact posPart_lip x y)

end M10i

section M10j
open StochKolmogorov.Persist
variable {n : ℕ}

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

end M10j

end ItoLib

end FlatM_P
-- ===== CM =====
section FlatM_CM
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5dK
/-! CORE route C5d, Kolmogorov instance (s26): the coefficients read through the box clamp
`boxP α β` (box `[α, β]^n` inside the open orthant) are globally Lipschitz and bounded, have the
form `s x (i, j) = aK i x * Γ j i`, and `|aK i x + aK i y| ≥ κ > 0` (Assumption 1.1 part 1). -/

variable {n : ℕ}

open StochKolmogorov.Persist

end C5dK
end ItoLib

end FlatM_CM
-- ===== CN =====
section FlatM_CN
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5g
/-! CORE route, s27: (1) `Γ` is invertible under Assumption 1.1 part 1; (2) a generic discrete
martingale `gmart` built from bounded past-measurable cell coefficients: measurability, second
moment, orthogonality and the Kolmogorov maximal inequality (used for the tracking estimate of
the steered chain). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0} {A B : ℕ → Ω → SDEDiffusion d}

end C5g
end ItoLib

end FlatM_CN
-- ===== QA =====
section FlatM_QA
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QA
/-! lemma_3_1 (aaf23e78) toolkit, part QA: continuous versions of Ito integrals.
Dyadic grid `gpt m l = l / 2^m`, the horizon-free step integral `stepM` (mesh `2^{-q}` on
`[0,q]`), its values at finer grid points, and a continuous-time maximal inequality for
differences of step integrals (via `gmart_max`). -/

noncomputable def hm (m : ℕ) : ℝ≥0 := 1 / 2 ^ m

noncomputable def gpt (m l : ℕ) : ℝ≥0 := ((l : ℝ) * (hm m : ℝ)).toNNReal

theorem hm_coe (m : ℕ) : (hm m : ℝ) = 1 / 2 ^ m := by simp [hm]

theorem gpt_coe (m l : ℕ) : (gpt m l : ℝ) = l / 2 ^ m := by
  unfold gpt
  rw [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg _)), hm_coe]
  ring

end QA
end ItoLib

end FlatM_QA
-- ===== QB =====
section FlatM_QB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QB
/-! lemma_3_1 toolkit, part QB: uniform `L²`-continuity of a bounded continuous integrand, and
the pathwise identification of `stepM q t` as the limit of `t`-grid Riemann sums whose
coefficients are the level-`q` left values (grid comparison, step 1). -/

end QB
end ItoLib

end FlatM_QB
-- ===== QC =====
section FlatM_QC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QC
/-! lemma_3_1 toolkit, part QC: grid comparison in `L²` and `stepM q t → J t` in probability
for every fixed `t` (bounded continuous adapted integrand). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

end QC
end ItoLib

end FlatM_QC
-- ===== QD =====
section FlatM_QD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QDan
/-! Pure analysis: a sequence of continuous functions with geometrically small successive
differences on growing intervals converges pointwise to a continuous limit. -/

end QDan

section QD

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

/-- **Continuous version of the Ito integral** of a bounded continuous adapted integrand. -/
theorem contIto_bdd (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C) :
    ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
      (∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (Jc t)) ∧
      (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H Jc := by
  exact (EthierKurtz.brownian_ito_integral_locality_and_continuity hW x₀).2.2.1 j H hHm hHa hHc C hC

end QD

end ItoLib

end FlatM_QD
-- ===== Q =====
section FlatM_Q
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10k
/-! M10k (b10 calculus): the cubic negative part `φ(v) = (v⁻)³` (C², `v φ' = 3φ`, `v² φ'' = 6φ`)
and the orthant test function `Hf r u = e^{-a} χ_r(|x|²) Σ_k φ(x_k)`. -/

variable {d : ℕ}

end M10k

section M10l
/-! M10l (b10 drift): generator of `Hf r` inside the ball and its global bound. -/
variable {d : ℕ}

end M10l

section M10m
/-! M10m (b10 expectation): `E Hf_r(X_t) ≤ Hf_r(x₀) + B/M` along `(X, X, A)`. -/
variable {Ω : Type*} {d : ℕ}

end M10m

end ItoLib

end FlatM_Q
-- ===== R =====
section FlatM_R
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10n
/-! M10n (b10 expectation and Markov step): `E Hf_r(X_t, A_t) ≤ Hf_r(x₀) + B/M`, and
`P{X stays in B̄_R on [0,t], ε < Φ(X_t)} ≤ (Hf_r(x₀) + B/M) / (e^{-ct} ε)`. -/
variable {Ω : Type*} {d : ℕ}

end M10n

end ItoLib

end FlatM_R
-- ===== S =====
section FlatM_S
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10o
/-! M10o (b10 done): orthant invariance of the Kolmogorov solutions, and the Markov statement. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M10o

end ItoLib

end FlatM_S
-- ===== U =====
section FlatM_U
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M11a
/-! M11a (lemma_3_1 clause 2): pathwise uniqueness for all times at once, and for the Kolmogorov
system. -/

theorem denseRange_rat_toNNReal : DenseRange fun q : ℚ => (q : ℝ).toNNReal := by
  have hs : DenseRange Real.toNNReal := Function.Surjective.denseRange fun x =>
    ⟨(x : ℝ), Real.toNNReal_coe⟩
  exact hs.comp Rat.denseRange_cast continuous_real_toNNReal

open StochKolmogorov.Persist

end M11a

section M11b
/-! M11b (lemma_3_1 clause 4a): `H < ∞`, i.e. `bracket35` is bounded above on the orthant. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M11b

end ItoLib

end FlatM_U
-- ===== QE =====
section FlatM_QE
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QEneg
variable {Ω : Type*} [MeasurableSpace Ω]

end QEneg

section QEF

end QEF

section QEface
open StochKolmogorov.Persist
variable {n : ℕ}

end QEface

end ItoLib

end FlatM_QE
-- ===== QF =====
section FlatM_QF
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QFgen
/-! Generic test function `F(x,y,a) = e^{-a} G(y)` along `(X, Y, A)`. -/
variable {d : ℕ}

end QFgen

section QFsat
/-! The concave saturation `h_m(u) = ∫₀ᵘ (1 - st(s - m)) ds`. -/

end QFsat

section QFell
/-! The logarithm `ℓ = log(1 + cᵀy) - Σ pᵢ log yᵢ` of `V`, its line derivatives, and bounds. -/
variable {n : ℕ}
open StochKolmogorov.Persist

end QFell

section QFalg
variable {n : ℕ}
open StochKolmogorov.Persist

end QFalg

section QFgenL
variable {n : ℕ}
open StochKolmogorov.Persist

end QFgenL

end ItoLib

end FlatM_QF
-- ===== QG =====
section FlatM_QG
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
open StochKolmogorov.Persist

section QG
/-! Clause 4b (3.6) of Lemma 3.1: `E V^δ₀(X_t) ≤ e^{δ₀ H t} V^δ₀(x)`. -/
variable {n : ℕ}

end QG

end ItoLib

end FlatM_QG
-- ===== QH =====
section FlatM_QH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QH
/-! Clause 1 toolkit (E1): the Ito isometry as an upper bound, `E J_t² ≤ E ∫₀ᵗ H²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QH

end ItoLib

end FlatM_QH
-- ===== QI =====
section FlatM_QI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QI
/-! Clause 1 toolkit (E3): weak maximal inequality for continuous versions of Ito integrals. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QI
end ItoLib

end FlatM_QI
-- ===== HK =====
section FlatM_HK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section HK
/-! 7ade6a3f K3ito toolkit: uniform-in-time convergence in probability of the step integrals
`stepM` to a continuous version of the Ito integral, first for bounded, then (by localisation)
for unbounded continuous adapted integrands. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem gpt_floor_le (t : ℝ≥0) (r : ℕ) : gpt r ⌊(t : ℝ) * 2 ^ r⌋₊ ≤ t := by
  rw [← NNReal.coe_le_coe, gpt_coe, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem gpt_floor_tendsto (t : ℝ≥0) :
    Tendsto (fun r => gpt r ⌊(t : ℝ) * 2 ^ r⌋₊) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have hup : ∀ r, (gpt r ⌊(t : ℝ) * 2 ^ r⌋₊ : ℝ) ≤ t := fun r => by
    exact_mod_cast gpt_floor_le t r
  have hlo : ∀ r, (t : ℝ) - 1 / 2 ^ r ≤ gpt r ⌊(t : ℝ) * 2 ^ r⌋₊ := fun r => by
    rw [gpt_coe, le_div_iff₀ (by positivity), sub_mul, one_div,
      inv_mul_cancel₀ (by positivity)]
    linarith [Nat.lt_floor_add_one ((t : ℝ) * 2 ^ r)]
  have hl : Tendsto (fun r : ℕ => (t : ℝ) - 1 / 2 ^ r) atTop (𝓝 t) := by
    have h0 : Tendsto (fun r : ℕ => (1 : ℝ) / 2 ^ r) atTop (𝓝 0) := by
      simpa [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa using h0.const_sub (t : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hup

end HK
end ItoLib

end FlatM_HK
-- ===== Doob =====
section FlatM_Doob
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section Doob
/-! 73c0fc13 step D1: Doob's L² maximal inequality for continuous versions of Itô integrals of
bounded continuous adapted integrands, with the integrated second moment `E ∫₀ᴺ G²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end Doob
end ItoLib

end FlatM_Doob
-- ===== Doob2 =====
section FlatM_Doob2
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section Doob2
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Doob's L² maximal inequality** for the continuous version of the Itô integral of a bounded
continuous adapted integrand: `λ² P(sup_{t ≤ N} |J t| > λ) ≤ 2d E ∫₀ᴺ G²`. -/
theorem doob_ito {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {G J : ℝ≥0 → Ω → ℝ}
    (hGm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (G s))
    (hGa : ∀ s, Measurable (G s)) (hGc : ∀ ω, Continuous fun s => G s ω) {C : ℝ}
    (hC : ∀ s ω, |G s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) G J)
    (hJc : ∀ ω, Continuous fun t => J t ω) (N : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |J t ω|} ≤
      2 * d * ∫ ω, (∫ u in (0 : ℝ)..(N : ℝ), G u.toNNReal ω ^ 2) ∂P := by
  exact EthierKurtz.brownian_ito_doob_maximal hW x₀ j hGm hGa hGc hC hJ hJc N hlam

end Doob2
end ItoLib

end FlatM_Doob2
-- ===== GateH =====
section FlatM_GateH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

/-! 73c0fc13 step D2: gated Doob maximal inequality for Itô integrals of unbounded continuous
adapted integrands (helpers copied from 8f909832_hl/C3.lean). -/

/-- Measurability of `ω ↦ ∫₀ˢ H(u) du` for `H` continuous in time and `m`-measurable up to `s`
(Carathéodory). -/
lemma measurable_integral_of_adapted {Ω : Type*} [m : MeasurableSpace Ω] {H : ℝ≥0 → Ω → ℝ}
    (s : ℝ≥0) (hm : ∀ u, u ≤ s → Measurable (H u)) (hc : ∀ ω, Continuous fun u => H u ω) :
    Measurable (fun ω => ∫ u in (0 : ℝ)..s.val, H u.toNNReal ω) := by
  set H' : ℝ → Ω → ℝ := fun u ω => H (min u.toNNReal s) ω with hH'
  have hH'c : ∀ ω, Continuous fun u => H' u ω :=
    fun ω => (hc ω).comp (continuous_real_toNNReal.min continuous_const)
  have hH'm : ∀ u, Measurable (H' u) := fun u => hm _ (min_le_right _ _)
  have hj : Measurable (Function.uncurry H') :=
    measurable_uncurry_of_continuous_of_measurable hH'c hH'm
  have hj' : StronglyMeasurable (Function.uncurry fun (ω : Ω) (u : ℝ) => H' u ω) :=
    (hj.comp measurable_swap).stronglyMeasurable
  have hint := hj'.integral_prod_right (ν := volume.restrict (Set.Ioc (0 : ℝ) s.val))
  have heq : (fun ω => ∫ u in (0 : ℝ)..s.val, H u.toNNReal ω) =
      fun ω => ∫ u, H' u ω ∂(volume.restrict (Set.Ioc (0 : ℝ) s.val)) := by
    funext ω
    rw [intervalIntegral.integral_of_le s.2]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    simp only [hH']
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hu.2)]
  rw [heq]; exact hint.measurable

/-- The gate `ρ(y) = 1 − min 1 (max 0 y)`. -/
noncomputable def rho (y : ℝ) : ℝ := 1 - min 1 (max 0 y)

lemma rho_nonneg (y : ℝ) : 0 ≤ rho y := by
  unfold rho; have := min_le_left (1 : ℝ) (max 0 y); linarith

lemma rho_le_one (y : ℝ) : rho y ≤ 1 := by
  unfold rho; have := le_min (zero_le_one' ℝ) (le_max_left 0 y); linarith

lemma rho_of_le {y : ℝ} (hy : y ≤ 0) : rho y = 1 := by
  unfold rho; rw [max_eq_left hy, min_eq_right zero_le_one]; ring

lemma rho_of_ge {y : ℝ} (hy : 1 ≤ y) : rho y = 0 := by
  unfold rho; rw [max_eq_right (by linarith), min_eq_left hy]; ring

lemma continuous_rho : Continuous rho := by
  unfold rho; fun_prop

lemma rho_sq_le_one (y : ℝ) : rho y ^ 2 ≤ 1 := by
  have h0 := rho_nonneg y; have h1 := rho_le_one y; nlinarith

/-- Pathwise gate bound: `∫₀ᵗ φ ρ(∫₀ᵘφ − A)² ≤ A + 1` for continuous `φ ≥ 0`. -/
lemma gate_bound (φ : ℝ → ℝ) (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u) {A : ℝ} (hA : 0 ≤ A)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, φ u * rho ((∫ v in (0 : ℝ)..u, φ v) - A) ^ 2 ≤ A + 1 := by
  set Q : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, φ v with hQ
  have hQc : Continuous Q := intervalIntegral.continuous_primitive
    (fun a b => hφc.intervalIntegrable a b) 0
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => φ u * rho (Q u - A) ^ 2) volume a b :=
    fun a b => (hφc.mul ((continuous_rho.comp (hQc.sub continuous_const)).pow 2)).intervalIntegrable a b
  have hle : ∀ b, 0 ≤ b → ∫ u in (0 : ℝ)..b, φ u * rho (Q u - A) ^ 2 ≤ Q b := by
    intro b hb
    refine intervalIntegral.integral_mono_on hb (hint 0 b) (hφc.intervalIntegrable 0 b) ?_
    intro u _
    have := rho_sq_le_one (Q u - A)
    have := hφ0 u
    nlinarith
  have hQmono : ∀ a b, a ≤ b → Q a ≤ Q b := by
    intro a b hab
    have : Q b = Q a + ∫ v in a..b, φ v := by
      simp only [hQ]
      rw [intervalIntegral.integral_add_adjacent_intervals (hφc.intervalIntegrable _ _)
        (hφc.intervalIntegrable _ _)]
    rw [this]
    have : 0 ≤ ∫ v in a..b, φ v := intervalIntegral.integral_nonneg hab (fun u _ => hφ0 u)
    linarith
  by_cases hT : Q t ≤ A + 1
  · exact (hle t ht).trans hT
  · replace hT := not_le.mp hT
    have hQ0 : Q 0 = 0 := by simp [hQ]
    obtain ⟨τ, hτ, hQτ⟩ : ∃ τ ∈ Set.Icc 0 t, Q τ = A + 1 :=
      intermediate_value_Icc ht hQc.continuousOn ⟨by rw [hQ0]; linarith, hT.le⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 τ) (hint τ t)]
    have h2 : ∫ u in τ..t, φ u * rho (Q u - A) ^ 2 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro u hu
        rw [Set.uIcc_of_le hτ.2] at hu
        have : 1 ≤ Q u - A := by have := hQmono τ u hu.1; linarith
        simp only [rho_of_ge this]; ring
    rw [h2, add_zero]
    exact (hle τ hτ.1).trans hQτ.le

/-- `∫ Φ ≤ c` for `0 ≤ Φ ≤ c` pointwise on a probability space (also if `Φ` is not integrable). -/
lemma integral_le_of_le_const {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Φ : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ ω, Φ ω ≤ c) :
    ∫ ω, Φ ω ∂P ≤ c := by
  by_cases hi : Integrable Φ P
  · calc ∫ ω, Φ ω ∂P ≤ ∫ _ω, c ∂P := integral_mono hi (integrable_const c) h
      _ = c := by simp
  · rw [integral_undef hi]; exact hc

end ItoLib.G73

end FlatM_GateH
-- ===== Gate =====
section FlatM_Gate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Gate
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma completedBrownianPast_mono' (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {s t : ℝ≥0} (hst : s ≤ t) :
    completedBrownianPast P W ξ s ≤ completedBrownianPast P W ξ t := by
  unfold completedBrownianPast
  refine sup_le_sup_right (sup_le_sup_right ?_ _) _
  refine iSup_le fun r => ?_
  have hr : r.val ≤ t := r.2.trans hst
  exact le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r.val, hr⟩

lemma toNNReal_le_of_mem' {t : ℝ≥0} {u : ℝ} (hu : u ∈ Set.uIcc (0 : ℝ) t.val) :
    u.toNNReal ≤ t := by
  rw [Set.uIcc_of_le t.2] at hu
  exact Real.toNNReal_le_iff_le_coe.mpr hu.2

end Gate
end ItoLib.G73

end FlatM_Gate
-- ===== Slln =====
section FlatM_Slln
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Slln
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end Slln
end ItoLib.G73

end FlatM_Slln
-- ===== GateSum =====
section FlatM_GateSum
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

/-! GateSum (a17b7893 s2): gated maximal inequality over DYADIC times for an Itô integral with no
continuity assumption (`gated_max_dy`, from ItoLib.G73.gated_max), its version for a continuous
modification `Y` of a finite sum of Itô integrals (`gated_max_Y`), and the continuous-time
martingale strong law under a pathwise linear bound on the quadratic variation (`slln_Y`). -/

namespace ItoLib.G73
open EthierKurtz ItoLib

section GateSum
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem gated_max_dy {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) (g : ℝ≥0 → Ω → ℝ)
    (hgm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (g s))
    (hga : ∀ s, Measurable (g s))
    (hgc : ∀ ω, Continuous fun s => g s ω) (c : ℝ) (L : ℝ≥0 → Ω → ℝ)
    (hL : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => g s ω * c) L)
    (N : ℕ) {A : ℝ} (hA : 0 ≤ A) {lam : ℝ} (hlam : 0 < lam) :
    P {ω | (∃ r k : ℕ, gpt r k ≤ (N : ℝ≥0) ∧ lam < |L (gpt r k) ω|) ∧
        ∫ u in (0 : ℝ)..(N : ℝ), g u.toNNReal ω ^ 2 ≤ A} ≤
      ENNReal.ofReal (2 * d * (c ^ 2 * (A + 1)) / lam ^ 2) := by
  set F := completedBrownianPast P W (fun _ => x₀) with hF
  have hFmono : ∀ {u s : ℝ≥0}, u ≤ s → F u ≤ F s := fun hus =>
    completedBrownianPast_mono' P W _ hus
  set T : ℝ≥0 := (N : ℝ≥0) with hT
  have hTv : T.val = (N : ℝ) := NNReal.coe_natCast N
  let cl : ℕ → ℝ → ℝ := fun M y => max (-(M : ℝ)) (min (M : ℝ) y)
  have hclc : ∀ M, Continuous (cl M) := fun M =>
    continuous_const.max (continuous_const.min continuous_id)
  have hclb : ∀ (M : ℕ) (y : ℝ), |cl M y| ≤ M := by
    intro M y
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hcl_eq : ∀ (M : ℕ) (y : ℝ), |y| ≤ M → cl M y = y := by
    intro M y hy
    obtain ⟨h1, h2⟩ := abs_le.mp hy
    simp only [cl]; rw [min_eq_right h2, max_eq_right h1]
  let gM : ℕ → ℝ≥0 → Ω → ℝ := fun M s ω => cl M (g s ω)
  let Q : ℕ → ℝ≥0 → Ω → ℝ := fun M s ω => ∫ u in (0 : ℝ)..s.val, gM M u.toNNReal ω ^ 2
  let G : ℕ → ℝ≥0 → Ω → ℝ := fun M s ω => gM M s ω * c * rho (Q M s ω - A)
  have hgMc : ∀ M ω, Continuous fun s => gM M s ω := fun M ω => (hclc M).comp (hgc ω)
  have hgMm : ∀ M s, Measurable[F s] (gM M s) := fun M s => (hclc M).measurable.comp (hgm s)
  have hgMa : ∀ M s, Measurable (gM M s) := fun M s => (hclc M).measurable.comp (hga s)
  have hQc : ∀ M ω, Continuous fun s : ℝ≥0 => Q M s ω := fun M ω =>
    (intervalIntegral.continuous_primitive (fun a b =>
      (((hgMc M ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable a b) 0).comp
      NNReal.continuous_coe
  have hQm : ∀ M s, Measurable[F s] (Q M s) := fun M s =>
    @measurable_integral_of_adapted Ω (F s) (fun u ω => gM M u ω ^ 2) s
      (fun u hu => ((hgMm M u).pow_const 2).mono (hFmono hu) le_rfl) (fun ω => (hgMc M ω).pow 2)
  have hQa : ∀ M s, Measurable (Q M s) := fun M s =>
    measurable_integral_of_adapted (H := fun u ω => gM M u ω ^ 2) s
      (fun u _ => (hgMa M u).pow_const 2) (fun ω => (hgMc M ω).pow 2)
  have hGc : ∀ M ω, Continuous fun s => G M s ω := fun M ω =>
    ((hgMc M ω).mul continuous_const).mul (continuous_rho.comp ((hQc M ω).sub continuous_const))
  have hGm : ∀ M s, Measurable[F s] (G M s) := fun M s =>
    ((hgMm M s).mul_const c).mul (continuous_rho.measurable.comp ((hQm M s).sub_const A))
  have hGa : ∀ M s, Measurable (G M s) := fun M s =>
    ((hgMa M s).mul_const c).mul (continuous_rho.measurable.comp ((hQa M s).sub_const A))
  have hGb : ∀ M s ω, |G M s ω| ≤ M * |c| := by
    intro M s ω
    have h1 := hclb M (g s ω)
    have h2 := rho_nonneg (Q M s ω - A)
    have h3 := rho_le_one (Q M s ω - A)
    have : |G M s ω| = |cl M (g s ω)| * |c| * rho (Q M s ω - A) := by
      simp only [G, gM, abs_mul, abs_of_nonneg h2]
    rw [this]
    calc |cl M (g s ω)| * |c| * rho (Q M s ω - A) ≤ M * |c| * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg c)) h3 h2
            (mul_nonneg (Nat.cast_nonneg M) (abs_nonneg c))
      _ = M * |c| := mul_one _
  have hex := fun M => contIto_bdd hW x₀ j (hGm M) (hGa M) (hGc M) (hGb M)
  choose LG hLGc _ _ _ hLG using hex
  -- Doob for the gated integral
  have hdoob : ∀ M, P {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |LG M t ω|} ≤
      ENNReal.ofReal (2 * d * (c ^ 2 * (A + 1)) / lam ^ 2) := by
    intro M
    have h := doob_ito hW x₀ j (hGm M) (hGa M) (hGc M) (hGb M) (hLG M) (hLGc M) N hlam
    have hint : ∫ ω, (∫ u in (0 : ℝ)..(N : ℝ), G M u.toNNReal ω ^ 2) ∂P ≤ c ^ 2 * (A + 1) := by
      refine integral_le_of_le_const (mul_nonneg (sq_nonneg c) (by linarith)) fun ω => ?_
      have hφc : Continuous fun u : ℝ => gM M u.toNNReal ω ^ 2 :=
        ((hgMc M ω).comp continuous_real_toNNReal).pow 2
      have hb := gate_bound (fun u : ℝ => gM M u.toNNReal ω ^ 2) hφc (fun u => sq_nonneg _) hA
        (Nat.cast_nonneg N)
      calc ∫ u in (0 : ℝ)..(N : ℝ), G M u.toNNReal ω ^ 2
          = c ^ 2 * ∫ u in (0 : ℝ)..(N : ℝ), gM M u.toNNReal ω ^ 2 *
              rho ((∫ v in (0 : ℝ)..u, gM M v.toNNReal ω ^ 2) - A) ^ 2 := by
            rw [← intervalIntegral.integral_const_mul]
            refine intervalIntegral.integral_congr fun u hu => ?_
            rw [Set.uIcc_of_le (Nat.cast_nonneg N)] at hu
            have hu' : (u.toNNReal).val = u := Real.coe_toNNReal u hu.1
            simp only [G, Q]
            rw [hu']
            ring
        _ ≤ c ^ 2 * (A + 1) := mul_le_mul_of_nonneg_left hb (sq_nonneg c)
    have hlam2 : 0 < lam ^ 2 := by positivity
    have hreal : P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |LG M t ω|} ≤
        2 * d * (c ^ 2 * (A + 1)) / lam ^ 2 := by
      rw [le_div_iff₀ hlam2]
      have h2 : 2 * (d : ℝ) * ∫ ω, (∫ u in (0 : ℝ)..(N : ℝ), G M u.toNNReal ω ^ 2) ∂P ≤
          2 * d * (c ^ 2 * (A + 1)) := mul_le_mul_of_nonneg_left hint (by positivity)
      linarith
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal hreal
  set S : Set Ω := {ω | (∃ r k : ℕ, gpt r k ≤ (N : ℝ≥0) ∧ lam < |L (gpt r k) ω|) ∧
      ∫ u in (0 : ℝ)..(N : ℝ), g u.toNNReal ω ^ 2 ≤ A} with hS
  set SM : ℕ → Set Ω := fun M => S ∩ {ω | ∀ s ≤ T, |g s ω| ≤ M} with hSMdef
  -- on `SM M` the gated integrand equals `g c` up to time `N`
  have hGeq : ∀ M, ∀ ω ∈ SM M, ∀ s ≤ T, G M s ω = g s ω * c := by
    intro M ω hω s hs
    have hgs : ∀ s', s' ≤ T → gM M s' ω = g s' ω := fun s' hs' => hcl_eq M _ (hω.2 s' hs')
    have hQs : Q M s ω ≤ A := by
      have heq : Q M s ω = ∫ u in (0 : ℝ)..s.val, g u.toNNReal ω ^ 2 := by
        refine intervalIntegral.integral_congr fun u hu => ?_
        show gM M u.toNNReal ω ^ 2 = g u.toNNReal ω ^ 2
        rw [hgs _ ((toNNReal_le_of_mem' hu).trans hs)]
      rw [heq]
      refine le_trans ?_ hω.1.2
      refine intervalIntegral.integral_mono_interval le_rfl s.2
        (by rw [← hTv]; exact_mod_cast hs)
        (Eventually.of_forall fun u => sq_nonneg _)
        ((((hgc ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _)
    simp only [G]
    rw [hgs _ hs, rho_of_le (by linarith), mul_one]
  have hSM : ∀ M, P (SM M) ≤ ENNReal.ofReal (2 * d * (c ^ 2 * (A + 1)) / lam ^ 2) := by
    intro M
    have hloc : ∀ r k : ℕ, ∀ᵐ ω ∂P, gpt r k ≤ T → ω ∈ SM M → LG M (gpt r k) ω = L (gpt r k) ω := by
      intro r k
      by_cases hk : gpt r k ≤ T
      · have h := hasBrownianItoIntegral_eq_on hW x₀ j (hGm M) (hGc M)
          (fun s => (hgm s).mul_const c) (fun ω => (hgc ω).mul continuous_const) (hLG M) hL
          (gpt r k) (SM M) (fun ω hω N' i hi => hGeq M ω hω _ ((dyTime_le _ hi).trans hk))
        filter_upwards [h] with ω hω _ hmem using hω hmem
      · exact ae_of_all _ fun ω h => absurd h hk
    have hall : ∀ᵐ ω ∂P, ∀ r k : ℕ, gpt r k ≤ T → ω ∈ SM M →
        LG M (gpt r k) ω = L (gpt r k) ω := by
      rw [ae_all_iff]; intro r; rw [ae_all_iff]; exact hloc r
    refine le_trans (measure_mono_ae ?_) (hdoob M)
    filter_upwards [hall] with ω hω hmem
    obtain ⟨r, k, hle, hlt⟩ := hmem.1.1
    refine ⟨gpt r k, hle, ?_⟩
    rw [hω r k hle hmem]
    exact hlt
  have hmono : Monotone SM := by
    intro M M' h ω hω
    exact ⟨hω.1, fun s hs => (hω.2 s hs).trans (by exact_mod_cast h)⟩
  have hU : ⋃ M, SM M = S := by
    ext ω; simp only [Set.mem_iUnion]; constructor
    · rintro ⟨M, h⟩; exact h.1
    · intro h
      obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
        (hgc ω).continuousOn
      obtain ⟨M, hM⟩ := exists_nat_ge B0
      refine ⟨M, h, fun s hs => ?_⟩
      have := hB0 s ⟨by positivity, hs⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans hM
  rw [← hU]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hSM

end GateSum
end ItoLib.G73

end FlatM_GateSum
-- ===== HLL =====
section FlatM_HLL

/-! Child `StochKolmogorov.Classify.log_lln_squares` (Hening-Nguyen arXiv:1704.06984v1, proof of Lemma 5.4 /
Theorem 5.2, p. 28): strong law of large numbers for `ln Xᵢ` along the times `m²`. Proof: Itô's formula for
`ln Xₖ` (smoothly floored), localized and de-localized by path continuity; gated L² bound for the martingale
part; Borel–Cantelli along `m²`. Uses the Proved platform theorems
`EthierKurtz.brownian_ito_integral_and_formula` and `EthierKurtz.brownian_ito_integral_locality_and_continuity`. -/

set_option autoImplicit false


section Part0
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

/-- Smooth floor at level `a/4`, equal to the identity on `[a/2, ∞)`. -/
noncomputable def psi (a y : ℝ) : ℝ :=
  Real.smoothTransition (4 * y / a - 1) * y +
    (1 - Real.smoothTransition (4 * y / a - 1)) * (a / 4)

lemma psi_contDiff (a : ℝ) : ContDiff ℝ ∞ (psi a) := by
  unfold psi
  have h1 : ContDiff ℝ ∞ (fun y : ℝ => Real.smoothTransition (4 * y / a - 1)) :=
    Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).div_const a).sub contDiff_const)
  exact (h1.mul contDiff_id).add ((contDiff_const.sub h1).mul contDiff_const)

lemma psi_eq {a y : ℝ} (ha : 0 < a) (hy : a / 2 ≤ y) : psi a y = y := by
  unfold psi
  have h : 1 ≤ 4 * y / a - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ ha]; linarith
  rw [Real.smoothTransition.one_of_one_le h]; ring

lemma psi_ge {a : ℝ} (ha : 0 < a) (y : ℝ) : a / 4 ≤ psi a y := by
  unfold psi
  set s := Real.smoothTransition (4 * y / a - 1)
  have hs0 : 0 ≤ s := Real.smoothTransition.nonneg _
  by_cases hy : a / 4 ≤ y
  · have : 0 ≤ s * (y - a / 4) := mul_nonneg hs0 (by linarith)
    nlinarith
  · have h : 4 * y / a - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_iff₀ ha]; linarith
    have : s = 0 := Real.smoothTransition.zero_of_nonpos h
    rw [this]; linarith

lemma psi_pos {a : ℝ} (ha : 0 < a) (y : ℝ) : 0 < psi a y :=
  lt_of_lt_of_le (by linarith) (psi_ge ha y)

/-- `log ∘ psi a`. -/
noncomputable def logPsi (a y : ℝ) : ℝ := Real.log (psi a y)

lemma logPsi_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (logPsi a) :=
  (psi_contDiff a).log (fun y => (psi_pos ha y).ne')

lemma logPsi_eq {a y : ℝ} (ha : 0 < a) (hy : a / 2 ≤ y) : logPsi a y = Real.log y := by
  unfold logPsi; rw [psi_eq ha hy]

lemma logPsi_eventuallyEq {a y : ℝ} (ha : 0 < a) (hy : a / 2 < y) :
    logPsi a =ᶠ[𝓝 y] Real.log := by
  filter_upwards [Ioi_mem_nhds hy] with z hz using logPsi_eq ha (le_of_lt hz)

lemma deriv_logPsi {a y : ℝ} (ha : 0 < a) (hy : a / 2 < y) : deriv (logPsi a) y = y⁻¹ := by
  rw [(logPsi_eventuallyEq ha hy).deriv_eq, Real.deriv_log]

lemma deriv_deriv_logPsi {a y : ℝ} (ha : 0 < a) (hy : a / 2 < y) :
    deriv (deriv (logPsi a)) y = -(y ^ 2)⁻¹ := by
  have h : deriv (logPsi a) =ᶠ[𝓝 y] fun z => z⁻¹ := by
    filter_upwards [Ioi_mem_nhds hy] with z hz using deriv_logPsi ha hz
  rw [h.deriv_eq, deriv_inv]

/-- Fréchet derivative of `v ↦ G (v k)`. -/
lemma hasFDerivAt_coord {n : ℕ} (G : ℝ → ℝ) (hG : Differentiable ℝ G) (k : Fin n)
    (v : SDEState n) :
    HasFDerivAt (fun w : SDEState n => G (w k))
      (deriv G (v k) • (EuclideanSpace.proj k : SDEState n →L[ℝ] ℝ)) v := by
  have h : HasFDerivAt (fun w : SDEState n => G (w k)) _ v :=
    ((hG (v k)).hasDerivAt.hasFDerivAt).comp v
      (EuclideanSpace.proj k : SDEState n →L[ℝ] ℝ).hasFDerivAt
  refine h.congr_fderiv ?_
  ext w; simp [mul_comm]

lemma fderiv_coord {n : ℕ} (G : ℝ → ℝ) (hG : Differentiable ℝ G) (k : Fin n) :
    fderiv ℝ (fun w : SDEState n => G (w k)) =
      fun v => deriv G (v k) • (EuclideanSpace.proj k : SDEState n →L[ℝ] ℝ) := by
  funext v; exact (hasFDerivAt_coord G hG k v).fderiv

lemma fderiv_coord_apply {n : ℕ} (G : ℝ → ℝ) (hG : Differentiable ℝ G) (k : Fin n)
    (v w : SDEState n) :
    fderiv ℝ (fun w : SDEState n => G (w k)) v w = deriv G (v k) * w k := by
  rw [fderiv_coord G hG k]; simp

lemma fderiv_fderiv_coord_apply {n : ℕ} (G : ℝ → ℝ) (hG : Differentiable ℝ G)
    (hG' : Differentiable ℝ (deriv G)) (k : Fin n) (v w w' : SDEState n) :
    fderiv ℝ (fderiv ℝ (fun w : SDEState n => G (w k))) v w w' =
      deriv (deriv G) (v k) * w k * w' k := by
  rw [fderiv_coord G hG k]
  have h := (hasFDerivAt_coord (deriv G) hG' k v).smul_const
    (EuclideanSpace.proj k : SDEState n →L[ℝ] ℝ)
  rw [h.fderiv]; simp [mul_comm, mul_left_comm]

/-- The test function of C1: `f_{a,k}(v) = log (psi a (v k))`. -/
noncomputable def fLog {n : ℕ} (a : ℝ) (k : Fin n) (v : SDEState n) : ℝ := logPsi a (v k)

lemma logPsi_diff {a : ℝ} (ha : 0 < a) : Differentiable ℝ (logPsi a) :=
  (logPsi_contDiff ha).differentiable (by simp)

lemma logPsi_diff' {a : ℝ} (ha : 0 < a) : Differentiable ℝ (deriv (logPsi a)) :=
  ((logPsi_contDiff ha).iterate_deriv 1).differentiable (by simp)

lemma fLog_contDiff {n : ℕ} {a : ℝ} (ha : 0 < a) (k : Fin n) : ContDiff ℝ 2 (fLog (n := n) a k) := by
  unfold fLog
  exact ((logPsi_contDiff ha).of_le (by first | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | simp | norm_cast | decide)).comp
    (EuclideanSpace.proj k : SDEState n →L[ℝ] ℝ).contDiff

lemma fderiv_fLog_single {n : ℕ} {a : ℝ} (ha : 0 < a) (k i : Fin n) (v : SDEState n) :
    fderiv ℝ (fLog a k) v (EuclideanSpace.single i 1) =
      if i = k then deriv (logPsi a) (v k) else 0 := by
  unfold fLog
  rw [fderiv_coord_apply _ (logPsi_diff ha) k]
  by_cases h : i = k
  · subst h; simp
  · simp [EuclideanSpace.single_apply, Ne.symm h, h]

lemma fderiv2_fLog_single {n : ℕ} {a : ℝ} (ha : 0 < a) (k i i' : Fin n) (v : SDEState n) :
    fderiv ℝ (fderiv ℝ (fLog a k)) v (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) =
      if i = k ∧ i' = k then deriv (deriv (logPsi a)) (v k) else 0 := by
  unfold fLog
  rw [fderiv_fderiv_coord_apply _ (logPsi_diff ha) (logPsi_diff' ha) k]
  by_cases h : i = k
  · by_cases h' : i' = k
    · subst h; subst h'; simp
    · subst h; simp [EuclideanSpace.single_apply, Ne.symm h', h']
  · simp [EuclideanSpace.single_apply, Ne.symm h, h]

lemma continuous_fderiv_fLog {n : ℕ} {a : ℝ} (ha : 0 < a) (k : Fin n) :
    Continuous (fderiv ℝ (fLog (n := n) a k)) :=
  (fLog_contDiff ha k).continuous_fderiv (by norm_num)

end StochKolmogorov.Classify.HL

end Part0


section Part1
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma continuous_posPart : Continuous (posPart (n := n)) := by
  unfold posPart
  first
  | fun_prop
  | exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).max
        continuous_const)

lemma posPart_mem (y : SDEState n) : posPart y ∈ orthant n := by
  intro i; simp [posPart]

lemma cont_comp_posPart {φ : SDEState n → ℝ} (h : ContinuousOn φ (orthant n)) :
    Continuous fun y => φ (posPart y) :=
  h.comp_continuous continuous_posPart posPart_mem

lemma posPart_eq_of_mem {y : SDEState n} (hy : y ∈ orthant n) : posPart y = y := by
  ext i; simp [posPart, max_eq_left (hy i)]

/-- Noise integrand of `ln Xₖ`: `gₖ(X⁺) Γⱼₖ`. -/
noncomputable def gInt (C : Coeffs n) (Y : ℝ≥0 → Ω → SDEState n) (k j : Fin n) :
    ℝ≥0 → Ω → ℝ :=
  fun s ω => C.g k (posPart (Y s ω)) * C.Γ j k

/-- Drift of `ln Xₖ`: `hₖ(y⁺) = fₖ(y⁺) − σₖₖ gₖ(y⁺)²/2`. -/
noncomputable def hInt (C : Coeffs n) (k : Fin n) (y : SDEState n) : ℝ :=
  C.f k (posPart y) - C.sig k k * C.g k (posPart y) ^ 2 / 2

lemma sig_self (C : Coeffs n) (k : Fin n) : C.sig k k = ∑ j, C.Γ j k * C.Γ j k := by
  simp [Coeffs.sig, Matrix.mul_apply]

lemma diffusion_apply (C : Coeffs n) (s : ℝ≥0) (y : SDEState n) (i j : Fin n) :
    diffusion C (s, y) (i, j) = y i * C.g i (posPart y) * C.Γ j i := by
  simp [diffusion]

lemma drift_apply (C : Coeffs n) (s : ℝ≥0) (y : SDEState n) (i : Fin n) :
    drift C (s, y) i = y i * C.f i (posPart y) := by
  simp [drift]

lemma le_t_of_dyadic (t : ℝ≥0) (N i : ℕ) (hi : i ≤ 2 ^ N) :
    (i : ℝ≥0) * t / 2 ^ N ≤ t := by
  rw [div_le_iff₀ (pow_pos (by norm_num) N)]
  calc (i : ℝ≥0) * t ≤ (2 ^ N : ℝ≥0) * t := by
        gcongr; exact_mod_cast hi
    _ = t * 2 ^ N := mul_comm _ _

lemma toNNReal_le_of_mem {t : ℝ≥0} {u : ℝ} (hu : u ∈ Set.uIcc (0 : ℝ) t.val) :
    u.toNNReal ≤ t := by
  rw [Set.uIcc_of_le t.2] at hu
  exact Real.toNNReal_le_iff_le_coe.mpr hu.2

set_option maxHeartbeats 1000000 in
/-- C1: Itô's formula for `ln Xₖ` on `{∀ s ≤ t, a ≤ Xₖ(s)}`. -/
theorem log_ito (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (hcont : ∀ i, ContinuousOn (C.f i) (orthant n) ∧ ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (hx : x ∈ orthant n) (k : Fin n) (L : Fin n → ℝ≥0 → Ω → ℝ)
    (hL : ∀ j, HasBrownianItoIntegral P (completedBrownianPast P B (fun _ => x))
        (fun s ω => B s ω j) (gInt C (X x) k j) (L j))
    (a : ℝ) (ha : 0 < a) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, (∀ s ≤ t, a ≤ X x s ω k) →
      Real.log (X x t ω k) = Real.log (x k) + (∑ j, L j t ω) +
        ∫ u in (0 : ℝ)..t.val, hInt C k (X x u.toNNReal ω) := by
  obtain ⟨hP, hB, hsol⟩ := hX
  obtain ⟨hXm, hXc, hXa, hX0, J, -, -, hJ, -, hXeq⟩ := hsol x hx
  obtain ⟨ito1, ito2, ito3⟩ := brownian_ito_integral_and_formula hB x
  obtain ⟨loc1, -, -, -⟩ := brownian_ito_integral_locality_and_continuity hB x
  have hfc : ∀ i, Continuous fun y : SDEState n => C.f i (posPart y) :=
    fun i => cont_comp_posPart (hcont i).1
  have hgc : ∀ i, Continuous fun y : SDEState n => C.g i (posPart y) :=
    fun i => cont_comp_posPart (hcont i).2
  -- coefficient processes
  set H : Fin n → Fin n → ℝ≥0 → Ω → ℝ := fun i j s ω => diffusion C (s, X x s ω) (i, j)
    with hHdef
  set b : Fin n → ℝ≥0 → Ω → ℝ := fun i s ω => drift C (s, X x s ω) i with hbdef
  have hHφ : ∀ i j, Continuous fun y : SDEState n => y i * C.g i (posPart y) * C.Γ j i :=
    fun i j => (((PiLp.continuous_apply 2 _ i).mul (hgc i)).mul continuous_const)
  have hbφ : ∀ i, Continuous fun y : SDEState n => y i * C.f i (posPart y) :=
    fun i => ((PiLp.continuous_apply 2 _ i).mul (hfc i))
  have hHeq : ∀ i j s ω, H i j s ω = X x s ω i * C.g i (posPart (X x s ω)) * C.Γ j i :=
    fun i j s ω => diffusion_apply C s _ i j
  have hbeq : ∀ i s ω, b i s ω = X x s ω i * C.f i (posPart (X x s ω)) :=
    fun i s ω => drift_apply C s _ i
  have hHm : ∀ i j s, Measurable[completedBrownianPast P B (fun _ => x) s] (H i j s) := by
    intro i j s
    have : H i j s = (fun y : SDEState n => y i * C.g i (posPart y) * C.Γ j i) ∘ X x s := by
      funext ω; exact hHeq i j s ω
    rw [this]; exact (hHφ i j).measurable.comp (hXa s)
  have hHc : ∀ i j ω, Continuous fun s => H i j s ω := by
    intro i j ω
    have : (fun s => H i j s ω) =
        (fun y : SDEState n => y i * C.g i (posPart y) * C.Γ j i) ∘ (fun s => X x s ω) := by
      funext s; exact hHeq i j s ω
    rw [this]; exact (hHφ i j).comp (hXc ω)
  have hbm : ∀ i s, Measurable[completedBrownianPast P B (fun _ => x) s] (b i s) := by
    intro i s
    have : b i s = (fun y : SDEState n => y i * C.f i (posPart y)) ∘ X x s := by
      funext ω; exact hbeq i s ω
    rw [this]; exact (hbφ i).measurable.comp (hXa s)
  have hbc : ∀ i ω, Continuous fun s => b i s ω := by
    intro i ω
    have : (fun s => b i s ω) = (fun y : SDEState n => y i * C.f i (posPart y)) ∘
        (fun s => X x s ω) := by
      funext s; exact hbeq i s ω
    rw [this]; exact (hbφ i).comp (hXc ω)
  -- the integrands of the Itô formula's martingale terms
  set f := fLog (n := n) a k with hfdef
  have hDc : Continuous (fderiv ℝ f) := continuous_fderiv_fLog ha k
  set Ki : Fin n → Fin n → ℝ≥0 → Ω → ℝ :=
    fun i j s ω => fderiv ℝ f (X x s ω) (EuclideanSpace.single i 1) * H i j s ω with hKidef
  have hKim : ∀ i j s, Measurable[completedBrownianPast P B (fun _ => x) s] (Ki i j s) := by
    intro i j s
    have hφ : Continuous fun y : SDEState n => fderiv ℝ f y (EuclideanSpace.single i 1) :=
      hDc.clm_apply continuous_const
    exact (hφ.measurable.comp (hXa s)).mul (hHm i j s)
  have hKic : ∀ i j ω, Continuous fun s => Ki i j s ω := by
    intro i j ω
    have hφ : Continuous fun y : SDEState n => fderiv ℝ f y (EuclideanSpace.single i 1) :=
      hDc.clm_apply continuous_const
    exact (hφ.comp (hXc ω)).mul (hHc i j ω)
  choose K hK using fun i j => ito1 j (Ki i j) (hKim i j) (hKic i j)
  have hform := @ito3 (by infer_instance) n (X x) hXm hXc hXa H (fun i j s ω => J s ω (i, j)) b
    hHm hHc hJ hbm hbc hXeq f (fLog_contDiff ha k) K hK t
  -- the martingale terms with `i ≠ k` vanish
  have hKz : ∀ i, i ≠ k → ∀ j, ∀ᵐ ω ∂P, K i j t ω = 0 := by
    intro i hi j
    have hb0 : ∀ s ω, |Ki i j s ω| ≤ 0 := by
      intro s ω; simp [hKidef, hfdef, fderiv_fLog_single ha, hi]
    obtain ⟨hm, hle, -⟩ := @ito2 hP j (Ki i j) (K i j) (hKim i j) (hKic i j) 0 hb0 (hK i j) t
    have hint : ∫ ω, K i j t ω ^ 2 ∂P = 0 :=
      le_antisymm (by simpa using hle) (integral_nonneg fun ω => sq_nonneg _)
    have := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (K i j t ω))
      hm.integrable_sq).mp hint
    filter_upwards [this] with ω hω
    simpa using hω
  -- the `i = k` terms are the Itô integrals `L j` on the event
  set E : Set Ω := {ω | ∀ s ≤ t, a ≤ X x s ω k} with hEdef
  have hloc : ∀ j, ∀ᵐ ω ∂P, ω ∈ E → K k j t ω = L j t ω := by
    intro j
    have hgm : ∀ s, Measurable[completedBrownianPast P B (fun _ => x) s] (gInt C (X x) k j s) :=
      fun s => ((hgc k).measurable.comp (hXa s)).mul measurable_const
    have hgcs : ∀ ω, Continuous fun s => gInt C (X x) k j s ω :=
      fun ω => ((hgc k).comp (hXc ω)).mul continuous_const
    refine loc1 j (Ki k j) (gInt C (X x) k j) (K k j) (L j) (hKim k j) (hKic k j) hgm hgcs
      (hK k j) (hL j) t E ?_
    intro ω hω N i hi
    have hs := hω _ (le_t_of_dyadic t N i hi)
    have hy : a / 2 < X x ((i : ℝ≥0) * t / 2 ^ N) ω k := by linarith
    have hy0 : X x ((i : ℝ≥0) * t / 2 ^ N) ω k ≠ 0 := by linarith
    simp only [hKidef, hfdef, fderiv_fLog_single ha, ite_true, if_true, hHeq, gInt]
    rw [deriv_logPsi ha hy]
    field_simp
  have hX0' : ∀ᵐ ω ∂P, X x 0 ω = x := hX0
  filter_upwards [hform, hX0', ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
      (show ∀ᵐ ω ∂P, i ≠ k → K i j t ω = 0 from by
        by_cases hi : i = k
        · exact Eventually.of_forall fun _ h => absurd hi h
        · filter_upwards [hKz i hi j] with ω h _ using h),
    ae_all_iff.mpr hloc] with ω hf h0 hz hl hE
  have hω : ω ∈ E := hE
  -- pathwise facts on the event
  have hpos : ∀ u ∈ Set.uIcc (0 : ℝ) t.val, a / 2 < X x u.toNNReal ω k :=
    fun u hu => by have := hE _ (toNNReal_le_of_mem hu); linarith
  have hcu : ∀ φ : SDEState n → ℝ, Continuous φ → Continuous fun u : ℝ => φ (X x u.toNNReal ω) :=
    fun φ hφ => hφ.comp ((hXc ω).comp continuous_real_toNNReal)
  -- left side and initial value
  have hlt : f (X x t ω) = Real.log (X x t ω k) := by
    simp only [hfdef, fLog]; exact logPsi_eq ha (by have := hE t le_rfl; linarith)
  have hl0 : f (X x 0 ω) = Real.log (x k) := by
    simp only [hfdef, fLog, h0]
    exact logPsi_eq ha (by have := hE 0 (by simp); rw [h0] at this; linarith)
  -- martingale part
  have hmart : (∑ i, ∑ j, K i j t ω) = ∑ j, L j t ω := by
    rw [Finset.sum_eq_single k (fun i _ hi => Finset.sum_eq_zero fun j _ => hz i j hi)
      (fun h => absurd (Finset.mem_univ k) h)]
    exact Finset.sum_congr rfl fun j _ => hl j hω
  -- drift part
  have hdrift : (∑ i, ∫ u in (0 : ℝ)..t.val,
      fderiv ℝ f (X x u.toNNReal ω) (EuclideanSpace.single i 1) * b i u.toNNReal ω) =
      ∫ u in (0 : ℝ)..t.val, C.f k (posPart (X x u.toNNReal ω)) := by
    rw [Finset.sum_eq_single k (fun i _ hi => by
        simp [hfdef, fderiv_fLog_single ha, hi]) (fun h => absurd (Finset.mem_univ k) h)]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have h1 := hpos u hu
    have h2 : X x u.toNNReal ω k ≠ 0 := by linarith
    simp only [hfdef, fderiv_fLog_single ha, if_pos rfl, ite_true, if_true, hbeq, deriv_logPsi ha h1]
    field_simp
  -- second-order part
  have hsec : (1 / 2 : ℝ) * ∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
      fderiv ℝ (fderiv ℝ f) (X x u.toNNReal ω) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1) * H i j u.toNNReal ω * H i' j u.toNNReal ω =
      ∫ u in (0 : ℝ)..t.val, -(C.sig k k * C.g k (posPart (X x u.toNNReal ω)) ^ 2 / 2) := by
    rw [Finset.sum_eq_single k (fun i _ hi => Finset.sum_eq_zero fun i' _ =>
        Finset.sum_eq_zero fun j _ => by simp [hfdef, fderiv2_fLog_single ha, hi])
      (fun h => absurd (Finset.mem_univ k) h)]
    rw [Finset.sum_eq_single k (fun i' _ hi' => Finset.sum_eq_zero fun j _ => by
        simp [hfdef, fderiv2_fLog_single ha, hi'])
      (fun h => absurd (Finset.mem_univ k) h)]
    have hj : ∀ j, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (fderiv ℝ f) (X x u.toNNReal ω) (EuclideanSpace.single k 1)
          (EuclideanSpace.single k 1) * H k j u.toNNReal ω * H k j u.toNNReal ω =
        ∫ u in (0 : ℝ)..t.val, -(C.g k (posPart (X x u.toNNReal ω)) ^ 2 * (C.Γ j k * C.Γ j k)) := by
      intro j
      refine intervalIntegral.integral_congr fun u hu => ?_
      have h1 := hpos u hu
      have h2 : X x u.toNNReal ω k ≠ 0 := by linarith
      simp only [hfdef, fderiv2_fLog_single ha, and_self, if_pos rfl, ite_true, if_true, hHeq,
        deriv_deriv_logPsi ha h1]
      field_simp
      try ring
    rw [Finset.sum_congr rfl fun j _ => hj j]
    rw [← intervalIntegral.integral_finsetSum (fun j _ =>
      (hcu (fun y => -(C.g k (posPart y) ^ 2 * (C.Γ j k * C.Γ j k)))
        ((((hgc k).pow 2).mul continuous_const).neg)).intervalIntegrable _ _)]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [sig_self, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  rw [← hlt, hf, hl0, hmart, hdrift, hsec]
  have hI1 : IntervalIntegrable (fun u : ℝ => C.f k (posPart (X x u.toNNReal ω))) volume 0 t.val :=
    (hcu _ (hfc k)).intervalIntegrable _ _
  have hI2 : IntervalIntegrable
      (fun u : ℝ => -(C.sig k k * C.g k (posPart (X x u.toNNReal ω)) ^ 2 / 2)) volume 0 t.val :=
    (hcu _ ((continuous_const.mul ((hgc k).pow 2)).div_const 2).neg).intervalIntegrable _ _
  rw [add_assoc, ← intervalIntegral.integral_add hI1 hI2]
  congr 2

end StochKolmogorov.Classify.HL

end Part1
section Part4
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

end StochKolmogorov.Classify.HL

end Part4

end FlatM_HLL
-- ===== V =====
section FlatM_V
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11c
/-! M11c: the orthant test-function machinery of Q.lean/R.lean with a general family of C²
nonnegative coordinate functions `φ k` in place of `(v⁻)³`. -/

variable {Ω : Type*} {d : ℕ}

variable {φ : Fin d → ℝ → ℝ} [hφ : Fact (∀ k, ContDiff ℝ 2 (φ k))]
  [hφ0 : Fact (∀ k v, 0 ≤ φ k v)]

end M11c

end ItoLib

end FlatM_V
-- ===== W =====
section FlatM_W
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11d
/-! M11d (lemma_3_1 clause 3, interior part): a solution started with `x_k > 0` has `X_t k ≠ 0`
almost surely at every fixed time. Test function `φ_δ(v) = 1/(v² + δ)`, with
`|φ_δ'(v) v| ≤ 2 φ_δ(v)` and `φ_δ''(v) v² ≤ 8 φ_δ(v)`. -/
open StochKolmogorov.Persist

variable {δ : ℝ}

variable {n : ℕ}

/-- `orthant_inv` for one solution (no solution family needed). -/
theorem orthant_inv1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω ∈ orthant n := by
  exact StochKolmogorov.Persist.orthant_invariance_closed P C B hB hC hx₀ hY t

end M11d

end ItoLib

end FlatM_W
-- ===== Y =====
section FlatM_Y
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12a
/-! M12a: the test-function machinery of V.lean for a single C² nonnegative function `ψ` of a
linear form `ℓ(x) = Σ_k cv_k x_k`, `Φ(x) = ψ(ℓ x)` (used with `ψ ≈ log(1+·)`). -/

variable {Ω : Type*} {d : ℕ}

variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

end M12a


section M12b
/-! M12b: the Lyapunov function `log(1 + cᵀx)` for (1.1): `E ∫₀ᵗ w(X_u) du ≤ log(1 + cᵀx) + log 2 + K t`
with `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)` and `K = max H 0` (`H` of (3.5)). -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- A solution from `x₀ ∈ ℝⁿ₊` stays in `ℝⁿ₊` at all times, a.s. -/
theorem orthant_inv_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) :
    ∀ᵐ ω ∂P, ∀ u, Y u ω ∈ orthant n := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, Y ((q : ℝ).toNNReal) ω ∈ orthant n :=
    ae_all_iff.2 fun q => orthant_inv1 P C B hB hC hx₀ hY _
  filter_upwards [hq] with ω hω u
  have hcl : IsClosed {s : ℝ≥0 | Y s ω ∈ orthant n} := orthant_isClosed.preimage (hY.2.1 ω)
  have hsub : Set.range (fun q : ℚ => (q : ℝ).toNNReal) ⊆ {s : ℝ≥0 | Y s ω ∈ orthant n} := by
    rintro _ ⟨q, rfl⟩; exact hω q
  have := hcl.closure_subset_iff.2 hsub
  rw [denseRange_rat_toNNReal.closure_range] at this
  exact this (Set.mem_univ u)

end M12b

end ItoLib

end FlatM_Y
-- ===== Z =====
section FlatM_Z
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12c
/-! M12c: invariant measures integrate the weight `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)`:
`∫ w dμ ≤ max H 0`, hence the Lyapunov integrands `fᵢ − σᵢᵢ gᵢ²/2` are `μ`-integrable. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M12c

end ItoLib

end FlatM_Z
-- ===== L33 =====
section FlatM_L33
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section L33
/-! L33 (lemma_3_2/3_3/3_4 work, s1 2026-10-30): generic Lyapunov bounds for the Kolmogorov family. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end L33

end ItoLib


end FlatM_L33
-- ===== L32 =====
section FlatM_L32
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section L32
/-! L32 (lemma_3_2 work, 15eaca53 s2 2026-10-30): the power Lyapunov function `(1 + cᵀx)^δ`. -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- Clause (3.8) of lemma_3_2. -/
theorem clause38 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (hn : 0 < n) :
    ∃ H₂ : ℝ, 0 < H₂ ∧
      (∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
        ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
            ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
              (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2)))) ∂P ≤
          ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t))) := by
  obtain ⟨-, H₂, -, hH₂, -, h38, -⟩ := StochKolmogorov.Persist.lemma_3_2 hn P C B X hX c γb hA δ₀ hδ₀
  exact ⟨H₂, hH₂, h38⟩

end L32

section L32T
/-! Dynkin bound keeping the terminal term (for (3.7)). -/
variable {Ω : Type*} {d : ℕ}
variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

end L32T

section L32U
open StochKolmogorov.Persist
variable {n : ℕ}

end L32U

section L32V
open StochKolmogorov.Persist
variable {n : ℕ}

end L32V

section L32G

end L32G

end ItoLib

end FlatM_L32
-- ===== Part2 =====
section FlatM_Part2
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Part2
variable {n : ℕ}

/-- The Persist copy of Classify coefficients (the two structures are identical). -/
def toP (C : StochKolmogorov.Classify.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

open StochKolmogorov.Classify

end Part2
end ItoLib.G73

end FlatM_Part2
-- ===== X41 =====
section FlatM_X41
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! X41 (eq_4_1, finite-`M` part): the minimax step of [SBA11, Lemma 4] for finitely many
boundary ergodic measures, by strict separation of a polytope from the closed negative orthant. -/

open StochKolmogorov.Persist EthierKurtz in
/-- `δ₀` of (3.2) exists: `δ₀ = γ_b / (3 S n + 3)` with `S = ∑ᵢⱼ |σᵢⱼ|`. -/
theorem exists_isDelta0 {n : ℕ} (C : Coeffs n) (γb : ℝ) (hγ : 0 < γb) :
    ∃ δ₀ : ℝ, IsDelta0 C γb δ₀ := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsij : ∀ i j, |C.sig i j| ≤ S := by
    intro i j
    calc |C.sig i j| ≤ ∑ j', |C.sig i j'| :=
          Finset.single_le_sum (f := fun j' => |C.sig i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C.sig i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hden : 0 < 3 * S * n + 3 := by positivity
  refine ⟨γb / (3 * S * n + 3), div_pos hγ hden, ?_, fun x _ => ?_⟩
  · rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [mul_nonneg hS0 (Nat.cast_nonneg (α := ℝ) n)]
  · set δ := γb / (3 * S * n + 3) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hγ hden).le
    set G : ℝ := ∑ i, C.g i x ^ 2 with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, |C.g i x * C.g j x * C.sig i j|
        ≤ S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |C.g i x| * |C.g j x| ≤ (C.g i x ^ 2 + C.g j x ^ 2) / 2 := by
        nlinarith [sq_nonneg (|C.g i x| - |C.g j x|), sq_abs (C.g i x), sq_abs (C.g j x)]
      calc |C.g i x| * |C.g j x| * |C.sig i j| ≤ ((C.g i x ^ 2 + C.g j x ^ 2) / 2) * S :=
            mul_le_mul h1 (hsij i j) (abs_nonneg _) (by positivity)
        _ = S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by ring
    have hsum : ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| ≤ S * n * G := by
      calc ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
          ≤ ∑ i : Fin n, ∑ j : Fin n, S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = S * n * G := by
            simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hG, ← Finset.sum_div]
            ring
    have hkey : δ * (3 * S * n + 3) = γb := by rw [hδ, div_mul_cancel₀ _ hden.ne']
    calc 3 * δ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ * G
        ≤ 3 * δ * (S * n * G) + δ * G := by nlinarith
      _ ≤ δ * (3 * S * n + 3) * G := by nlinarith [mul_nonneg hδ0 hG0]
      _ = γb * G := by rw [hkey]

end ItoLib

end FlatM_X41
-- ===== T1b =====
section FlatM_T1b

/-! T1b `short_time_positivity` (a17b7893 s3): Hening-Nguyen 1704.06984 (5.15)/(5.19) at any radius.
For `x ∈ ℝⁿ₊` with `‖x‖₁ ≤ R` and `xᵢ > ε₂`, `P(Xᵢ(t) > β ∀ t ≤ T) > 1 - ε₁`, uniformly.
Proof: Itô for `ln Xᵢ` at dyadic times (`HL.log_ito`), Markov on the expected Lyapunov integral
(`clause38` = Persist.lemma_3_2 (3.8)) gating both `∫|hᵢ|` and `∫gᵢ²`, the gated dyadic maximal
inequality (`ItoLib.G73.gated_max_dy`), and a first-drop argument along dyadic times. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace StochKolmogorov.Classify.STP
open StochKolmogorov.Classify EthierKurtz ItoLib

/-- First-drop argument along dyadic times. -/
theorem first_drop (f : ℝ≥0 → ℝ) (hf : Continuous f) {β : ℝ} (hβ : 0 < β) (T : ℝ≥0)
    (h0 : β < f 0)
    (H : ∀ r k : ℕ, gpt r k ≤ T → (∀ s ≤ gpt r k, β ≤ f s) → 2 * β ≤ f (gpt r k)) :
    ∀ t ≤ T, β < f t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t0, ht0T, ht0⟩ := hcon
  set S : Set ℝ≥0 := {s | s ≤ t0 ∧ f s ≤ β} with hS
  have hSc : IsClosed S := (isClosed_le continuous_id continuous_const).inter
    (isClosed_le hf continuous_const)
  have hSne : S.Nonempty := ⟨t0, le_rfl, ht0⟩
  set τ := sInf S with hτdef
  have hτ : τ ∈ S := hSc.csInf_mem hSne (OrderBot.bddBelow S)
  have hbelow : ∀ s, s < τ → β < f s := by
    intro s hs
    by_contra hfs
    push Not at hfs
    have hsS : s ∈ S := ⟨hs.le.trans hτ.1, hfs⟩
    exact absurd (csInf_le (OrderBot.bddBelow S) hsS) (not_le.mpr hs)
  have hτ0 : 0 < τ := by
    rw [pos_iff_ne_zero]
    intro h
    have h2 : f τ ≤ β := hτ.2
    rw [h] at h2
    linarith
  have hfτ : β ≤ f τ := by
    by_contra hlt
    push Not at hlt
    have hU : f ⁻¹' Iio β ∈ 𝓝 τ := hf.continuousAt.preimage_mem_nhds (Iio_mem_nhds hlt)
    obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hU ⟨0, hτ0⟩
    obtain ⟨s, hls, hsτ⟩ := exists_between hl
    have h1 : f s < β := hsub ⟨hls, hsτ.le⟩
    linarith [hbelow s hsτ]
  have hall : ∀ s ≤ τ, β ≤ f s := by
    intro s hs
    rcases eq_or_lt_of_le hs with h | h
    · rw [h]; exact hfτ
    · exact (hbelow s h).le
  have hq : ∀ r, 2 * β ≤ f (gpt r ⌊(τ : ℝ) * 2 ^ r⌋₊) := fun r =>
    H r _ ((gpt_floor_le τ r).trans (hτ.1.trans ht0T))
      (fun s hs => hall s (hs.trans (gpt_floor_le τ r)))
  have hlim : Tendsto (fun r => f (gpt r ⌊(τ : ℝ) * 2 ^ r⌋₊)) atTop (𝓝 (f τ)) :=
    (hf.tendsto τ).comp (gpt_floor_tendsto τ)
  have h3 := ge_of_tendsto' hlim hq
  have h2 : f τ ≤ β := hτ.2
  linarith

/-- Real integral bounded through a lintegral bound. -/
theorem int_le_of_lint {φ ψ : ℝ → ℝ} {N : ℝ} (hN : 0 ≤ N) (hφc : Continuous φ)
    (hφ0 : ∀ u, 0 ≤ φ u) {K : ℝ} (hK : 0 ≤ K) (hle : ∀ u, φ u ≤ K * ψ u) {A : ℝ} (hA : 0 ≤ A)
    (hQ : ∫⁻ u in Icc 0 N, ENNReal.ofReal (ψ u) ≤ ENNReal.ofReal A) :
    ∫ u in (0 : ℝ)..N, φ u ≤ K * A := by
  have h1 : ENNReal.ofReal (∫ u in (0 : ℝ)..N, φ u) ≤ ENNReal.ofReal (K * A) := by
    rw [intervalIntegral.integral_of_le hN, ofReal_integral_eq_lintegral_ofReal
      (hφc.integrableOn_Icc.mono_set Ioc_subset_Icc_self) (ae_of_all _ hφ0)]
    calc ∫⁻ u in Ioc 0 N, ENNReal.ofReal (φ u)
        ≤ ∫⁻ u in Icc 0 N, ENNReal.ofReal (φ u) := lintegral_mono_set Ioc_subset_Icc_self
      _ ≤ ∫⁻ u in Icc 0 N, ENNReal.ofReal K * ENNReal.ofReal (ψ u) := by
          refine lintegral_mono fun u => ?_
          rw [← ENNReal.ofReal_mul hK]
          exact ENNReal.ofReal_le_ofReal (hle u)
      _ = ENNReal.ofReal K * ∫⁻ u in Icc 0 N, ENNReal.ofReal (ψ u) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal A := by gcongr
      _ = ENNReal.ofReal (K * A) := (ENNReal.ofReal_mul hK).symm
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK hA)).1 h1

variable {n : ℕ}

/-- Lyapunov weight of (3.8), read through `posPart`. -/
noncomputable def Wf (C : Coeffs n) (c : SDEState n) (δ₀ : ℝ) (y : SDEState n) : ℝ :=
  (1 + ∑ k, c k * posPart y k) ^ δ₀ *
    (1 + ∑ k, (|C.f k (posPart y)| + |C.g k (posPart y)| ^ 2))

theorem Wf_ge (C : Coeffs n) {c : SDEState n} (hc : c ∈ openOrthant n) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (y : SDEState n) :
    1 + ∑ k, (|C.f k (posPart y)| + |C.g k (posPart y)| ^ 2) ≤ Wf C c δ₀ y := by
  have hF : 0 ≤ 1 + ∑ k, (|C.f k (posPart y)| + |C.g k (posPart y)| ^ 2) :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => add_nonneg (abs_nonneg _) (sq_nonneg _))
  have hs : 0 ≤ ∑ k, c k * posPart y k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (HL.posPart_mem y k)
  exact le_mul_of_one_le_left hF (Real.one_le_rpow (by linarith) hδ)

theorem term_le (C : Coeffs n) (y : SDEState n) (i : Fin n) :
    |C.f i (posPart y)| + |C.g i (posPart y)| ^ 2 ≤
      1 + ∑ k, (|C.f k (posPart y)| + |C.g k (posPart y)| ^ 2) := by
  have := Finset.single_le_sum (f := fun k => |C.f k (posPart y)| + |C.g k (posPart y)| ^ 2)
    (fun k _ => add_nonneg (abs_nonneg _) (sq_nonneg _)) (Finset.mem_univ i)
  linarith

theorem hInt_le (C : Coeffs n) {c : SDEState n} (hc : c ∈ openOrthant n) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (y : SDEState n) (i : Fin n) :
    |HL.hInt C i y| ≤ (1 + ∑ k, |C.sig k k|) * Wf C c δ₀ y := by
  have hsi : |C.sig i i| ≤ ∑ k, |C.sig k k| :=
    Finset.single_le_sum (f := fun k => |C.sig k k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  have hS0 : 0 ≤ ∑ k, |C.sig k k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  set a := |C.f i (posPart y)| with ha
  set b := |C.g i (posPart y)| ^ 2 with hb
  have ha0 : 0 ≤ a := abs_nonneg _
  have hb0 : 0 ≤ b := sq_nonneg _
  have h1 : |HL.hInt C i y| ≤ a + |C.sig i i| * b := by
    unfold HL.hInt
    have e : C.g i (posPart y) ^ 2 = b := by rw [hb, sq_abs]
    rw [e]
    calc |C.f i (posPart y) - C.sig i i * b / 2|
        ≤ |C.f i (posPart y)| + |C.sig i i * b / 2| := abs_sub _ _
      _ = a + |C.sig i i| * b / 2 := by
          rw [abs_div, abs_mul, abs_of_nonneg hb0, abs_two]
      _ ≤ a + |C.sig i i| * b := by nlinarith [abs_nonneg (C.sig i i)]
  have h2 : a + |C.sig i i| * b ≤ (1 + ∑ k, |C.sig k k|) * (a + b) := by
    nlinarith [mul_le_mul_of_nonneg_right hsi hb0]
  have h3 := term_le C y i
  have h4 := Wf_ge C hc hδ y
  have hK : 0 ≤ 1 + ∑ k, |C.sig k k| := by linarith
  calc |HL.hInt C i y| ≤ (1 + ∑ k, |C.sig k k|) * (a + b) := h1.trans h2
    _ ≤ (1 + ∑ k, |C.sig k k|) * Wf C c δ₀ y :=
        mul_le_mul_of_nonneg_left (h3.trans h4) hK

theorem gsq_le (C : Coeffs n) {c : SDEState n} (hc : c ∈ openOrthant n) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (y : SDEState n) (i : Fin n) :
    C.g i (posPart y) ^ 2 ≤ 1 * Wf C c δ₀ y := by
  have h3 := term_le C y i
  have h4 := Wf_ge C hc hδ y
  rw [← sq_abs]
  linarith [abs_nonneg (C.f i (posPart y))]

set_option maxHeartbeats 1000000 in
/-- T1b (paper (5.15)/(5.19)): short-time positivity of a coordinate, uniformly on `‖x‖₁ ≤ R`. -/
theorem short_time_positivity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ R T : ℝ, 0 < T → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → ∃ β : ℝ, 0 < β ∧
      ∀ i, ∀ x ∈ orthant n, l1 x ≤ R → ε₂ < x i →
        1 - ε₁ < (P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i}).toReal := by
  intro R T hT ε₁ ε₂ hε₁ hε₂
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    exact ⟨1, one_pos, fun i => Fin.elim0 i⟩
  have hP : IsProbabilityMeasure P := hX.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hcont : ∀ i, ContinuousOn (C.f i) (orthant n) ∧ ContinuousOn (C.g i) (orthant n) :=
    fun i => ⟨(hA.2.1 i).1.continuousOn, (hA.2.1 i).2.continuousOn⟩
  obtain ⟨δ₀, hδ₀⟩ := ItoLib.exists_isDelta0 (G73.toP C) γb hA.2.2.2.1
  have hδ0 : 0 ≤ δ₀ := hδ₀.1.le
  have hXP : StochKolmogorov.Persist.IsSolutionFamily P (G73.toP C) B X := hX
  obtain ⟨H₂, hH₂, h38⟩ := ItoLib.clause38 P (G73.toP C) B X hXP c γb hA δ₀ hδ₀ hn
  set N : ℕ := ⌈T⌉₊ with hNdef
  have hTN : T ≤ (N : ℝ) := Nat.le_ceil T
  have hN0 : (0 : ℝ≥0) < (N : ℝ≥0) := by
    have : 0 < N := Nat.ceil_pos.2 hT
    exact_mod_cast this
  have hNr : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  set cs : ℝ := ∑ k, c k with hcs
  have hcs0 : 0 ≤ cs := Finset.sum_nonneg fun k _ => (hc k).le
  have hcR : 0 ≤ cs * max R 0 := mul_nonneg hcs0 (le_max_right R 0)
  set AR : ℝ := (1 + cs * max R 0) ^ δ₀ with hAR
  have hAR0 : 0 ≤ AR := Real.rpow_nonneg (by linarith) _
  set B0 : ℝ := H₂ * (AR + N) with hB0
  have hB00 : 0 ≤ B0 := mul_nonneg hH₂.le (by linarith)
  set K1 : ℝ := 1 + ∑ k, |C.sig k k| with hK1
  have hK10 : 0 ≤ K1 := by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => abs_nonneg (C.sig k k)
    linarith
  set A : ℝ := 4 * B0 / ε₁ + 1 with hAdef
  have hA1 : 0 < A := by
    have := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hB00) hε₁.le
    linarith
  set G : ℝ := ∑ a, ∑ b, C.Γ a b ^ 2 + 1 with hG
  have hG1 : 0 < G := by
    have := Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_nonneg fun b (_ : b ∈ Finset.univ) => sq_nonneg (C.Γ a b)
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set lam : ℝ := 8 * n * (n + 1) * G * (A + 1) / ε₁ + 1 with hlam
  have hlam1 : 1 ≤ lam := by
    have : 0 ≤ 8 * (n : ℝ) * (n + 1) * G * (A + 1) / ε₁ :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) hG1.le) (by linarith)) hε₁.le
    linarith
  have hlam0 : 0 < lam := by linarith
  set c0 : ℝ := Real.log ε₂ - n * lam - K1 * A with hc0
  refine ⟨Real.exp c0 / 2, by positivity, ?_⟩
  set β : ℝ := Real.exp c0 / 2 with hβdef
  have hβ : 0 < β := by rw [hβdef]; positivity
  have h2β : 2 * β = Real.exp c0 := by rw [hβdef]; ring
  have hβε : β < ε₂ := by
    have hc0l : c0 ≤ Real.log ε₂ := by
      rw [hc0]
      have q1 := mul_nonneg hn0 hlam0.le
      have q2 := mul_nonneg hK10 hA1.le
      linarith
    have h := Real.exp_le_exp.2 hc0l
    rw [Real.exp_log hε₂] at h
    linarith
  intro i x hx hxR hxi
  obtain ⟨hXm, hXc, hXa, hX0, -⟩ := hX.2.2 x hx
  obtain ⟨ito1, -, -⟩ := brownian_ito_integral_and_formula hX.2.1 x
  have hgc : Continuous fun y : SDEState n => C.g i (posPart y) :=
    HL.cont_comp_posPart (hcont i).2
  have hgm : ∀ j s, Measurable[completedBrownianPast P B (fun _ => x) s]
      (HL.gInt C (X x) i j s) :=
    fun j s => (hgc.measurable.comp (hXa s)).mul measurable_const
  have hgcs : ∀ j ω, Continuous fun s => HL.gInt C (X x) i j s ω :=
    fun j ω => (hgc.comp (hXc ω)).mul continuous_const
  choose L hL using fun j => ito1 j (HL.gInt C (X x) i j) (hgm j) (hgcs j)
  have hform : ∀ᵐ ω ∂P, ∀ r k : ℕ, (∀ s ≤ gpt r k, β ≤ X x s ω i) →
      Real.log (X x (gpt r k) ω i) = Real.log (x i) + (∑ j, L j (gpt r k) ω) +
        ∫ u in (0 : ℝ)..(gpt r k).val, HL.hInt C i (X x u.toNNReal ω) :=
    ae_all_iff.2 fun r => ae_all_iff.2 fun k =>
      HL.log_ito P C B X hX hcont x hx i L hL β hβ (gpt r k)
  have hall : ∀ᵐ ω ∂P, ∀ u, X x u ω ∈ orthant n :=
    ItoLib.orthant_inv_all P (G73.toP C) B hX.2.1 hA.2.1 hx (hX.2.2 x hx)
  have hWc : Continuous (Wf C c δ₀) := by
    unfold Wf
    have hco : ∀ k, Continuous fun y : SDEState n => posPart y k :=
      fun k => (PiLp.continuous_apply 2 _ k).comp HL.continuous_posPart
    refine Continuous.mul ?_ ?_
    · refine Continuous.rpow_const ?_ fun _ => Or.inr hδ0
      exact continuous_const.add (continuous_finsetSum _ fun k _ => continuous_const.mul (hco k))
    · refine continuous_const.add (continuous_finsetSum _ fun k _ => ?_)
      exact (HL.cont_comp_posPart (hcont k).1).abs.add
        ((HL.cont_comp_posPart (hcont k).2).abs.pow 2)
  set Q : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ u in Icc (0 : ℝ) N, ENNReal.ofReal (Wf C c δ₀ (X x u.toNNReal ω)) with hQdef
  have hjoint : Measurable (Function.uncurry (X x)) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hXc ω) hXm
  have hQm : Measurable Q := by
    have hF : Measurable fun p : Ω × ℝ => ENNReal.ofReal (Wf C c δ₀ (X x p.2.toNNReal p.1)) :=
      ENNReal.measurable_ofReal.comp (hWc.measurable.comp
        (hjoint.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)))
    show Measurable fun ω => ∫⁻ u in Icc (0 : ℝ) N, ENNReal.ofReal (Wf C c δ₀ (X x u.toNNReal ω))
    exact hF.lintegral_prod_right'
  have hcx : ∑ k, c k * x k ≤ cs * max R 0 := by
    have hl : ∀ k, x k ≤ max R 0 := fun k => by
      have h1 : x k ≤ l1 x := by
        have := Finset.single_le_sum (f := fun k => |x k|) (fun k _ => abs_nonneg _)
          (Finset.mem_univ k)
        exact (le_abs_self _).trans this
      exact (h1.trans hxR).trans (le_max_left _ _)
    rw [hcs, Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hl k) (hc k).le
  have hQE : ∫⁻ ω, Q ω ∂P ≤ ENNReal.ofReal B0 := by
    have e : ∫⁻ ω, Q ω ∂P = ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) ((N : ℝ≥0) : ℝ),
        ENNReal.ofReal ((1 + ∑ k, c k * X x s.toNNReal ω k) ^ δ₀ *
          (1 + ∑ k, (|C.f k (X x s.toNNReal ω)| + |C.g k (X x s.toNNReal ω)| ^ 2)))) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hall] with ω hω
      have hpp : ∀ u, posPart (X x u ω) = X x u ω := fun u => HL.posPart_eq_of_mem (hω u)
      simp only [hQdef, Wf, hpp, NNReal.coe_natCast]
    rw [e]
    refine (h38 x hx (N : ℝ≥0) hN0).trans (ENNReal.ofReal_le_ofReal ?_)
    have hs0 : 0 ≤ ∑ k, c k * x k := Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hx k)
    have hle : (1 + ∑ k, c k * x k) ^ δ₀ ≤ AR := by
      rw [hAR]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hδ0
    rw [NNReal.coe_natCast, hB0]
    exact mul_le_mul_of_nonneg_left (by linarith) hH₂.le
  set E0 : Set Ω := {ω | ENNReal.ofReal A ≤ Q ω} with hE0
  have hPE0 : P E0 ≤ ENNReal.ofReal (ε₁ / 4) := by
    refine (meas_ge_le_lintegral_div hQm.aemeasurable
      (ENNReal.ofReal_pos.2 hA1).ne' ENNReal.ofReal_ne_top).trans ?_
    refine (ENNReal.div_le_div_right hQE _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos hA1]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : ε₁ * (4 * B0 / ε₁) = 4 * B0 := by field_simp
    have hAB : 4 * B0 ≤ ε₁ * A := by
      rw [hAdef, mul_add, e1]; linarith
    rw [div_le_div_iff₀ hA1 (by norm_num)]
    linarith
  set Gs : Fin n → Set Ω := fun j => {ω | (∃ r k : ℕ, gpt r k ≤ (N : ℝ≥0) ∧
      lam < |L j (gpt r k) ω|) ∧
      ∫ u in (0 : ℝ)..(N : ℝ), C.g i (posPart (X x u.toNNReal ω)) ^ 2 ≤ A} with hGs
  have hPG : ∀ j, P (Gs j) ≤ ENNReal.ofReal (ε₁ / (4 * (n + 1))) := by
    intro j
    have hg := ItoLib.G73.gated_max_dy hX.2.1 x j (fun s ω => C.g i (posPart (X x s ω)))
      (fun s => hgc.measurable.comp (hXa s)) (fun s => hgc.measurable.comp (hXm s))
      (fun ω => hgc.comp (hXc ω)) (C.Γ j i) (L j) (hL j) N hA1.le hlam0
    refine hg.trans (ENNReal.ofReal_le_ofReal ?_)
    have hΓ : C.Γ j i ^ 2 ≤ G := by
      have h1 : C.Γ j i ^ 2 ≤ ∑ b, C.Γ j b ^ 2 :=
        Finset.single_le_sum (f := fun b => C.Γ j b ^ 2) (fun b _ => sq_nonneg _)
          (Finset.mem_univ i)
      have h2 : ∑ b, C.Γ j b ^ 2 ≤ ∑ a, ∑ b, C.Γ a b ^ 2 :=
        Finset.single_le_sum (f := fun a => ∑ b, C.Γ a b ^ 2)
          (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ j)
      linarith
    have hlsq : lam ≤ lam ^ 2 := by
      have q := mul_le_mul_of_nonneg_left hlam1 hlam0.le
      rw [mul_one] at q; rw [sq]; exact q
    have hnum : 2 * n * (C.Γ j i ^ 2 * (A + 1)) ≤ 2 * n * (G * (A + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΓ (by linarith)) (by positivity)
    have hlam' : ε₁ * lam = 8 * n * (n + 1) * G * (A + 1) + ε₁ := by
      rw [hlam]; field_simp
    have h4n : (0 : ℝ) ≤ 4 * (n + 1) := by positivity
    rw [div_le_div_iff₀ (pow_pos hlam0 2) (by positivity)]
    have q5 := mul_le_mul_of_nonneg_right hnum h4n
    have q6 := mul_le_mul_of_nonneg_left hlsq hε₁.le
    linarith
  set S : Set Ω := {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i} with hSdef
  have hsub : Sᶜ ≤ᵐ[P] ((E0 ∪ ⋃ j, Gs j : Set Ω)) := by
    filter_upwards [hform, hX0] with ω hω h0ω
    change ω ∈ Sᶜ → ω ∈ E0 ∪ ⋃ j, Gs j
    intro hnS
    by_contra hno
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hno
    obtain ⟨hnE, hnG⟩ := hno
    apply hnS
    have hnE' : ¬ (ENNReal.ofReal A ≤ Q ω) := hnE
    have hQ : Q ω ≤ ENNReal.ofReal A := (not_le.1 hnE').le
    have hp : Continuous fun u : ℝ => X x u.toNNReal ω := (hXc ω).comp continuous_real_toNNReal
    have hhc : Continuous fun u : ℝ => HL.hInt C i (X x u.toNNReal ω) :=
      ((HL.cont_comp_posPart (hcont i).1).comp hp).sub
        ((continuous_const.mul ((hgc.comp hp).pow 2)).div_const 2)
    have hI : ∫ u in (0 : ℝ)..(N : ℝ), |HL.hInt C i (X x u.toNNReal ω)| ≤ K1 * A :=
      int_le_of_lint hNr hhc.abs (fun u => abs_nonneg _) hK10
        (fun u => hInt_le C hc hδ0 _ i) hA1.le hQ
    have hgate : ∫ u in (0 : ℝ)..(N : ℝ), C.g i (posPart (X x u.toNNReal ω)) ^ 2 ≤ A := by
      have := int_le_of_lint (φ := fun u => C.g i (posPart (X x u.toNNReal ω)) ^ 2) hNr
        ((hgc.comp hp).pow 2) (fun u => sq_nonneg _) zero_le_one
        (fun u => gsq_le C hc hδ0 _ i) hA1.le hQ
      rw [one_mul] at this
      exact this
    have hLb : ∀ j, ∀ r k : ℕ, gpt r k ≤ (N : ℝ≥0) → |L j (gpt r k) ω| ≤ lam := by
      intro j r k hq
      by_contra hlt
      exact hnG j ⟨⟨r, k, hq, not_le.1 hlt⟩, hgate⟩
    have hx0 : X x 0 ω = x := h0ω
    have hfc : Continuous fun t => X x t ω i := (PiLp.continuous_apply 2 _ i).comp (hXc ω)
    have hH : ∀ r k : ℕ, gpt r k ≤ (N : ℝ≥0) → (∀ s ≤ gpt r k, β ≤ X x s ω i) →
        2 * β ≤ X x (gpt r k) ω i := by
      intro r k hq hge
      have hqr : ((gpt r k : ℝ≥0) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hq
      have hfq : 0 < X x (gpt r k) ω i := hβ.trans_le (hge _ le_rfl)
      have hlog := hω r k hge
      have hsumL : -((n : ℝ) * lam) ≤ ∑ j, L j (gpt r k) ω := by
        have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (abs_le.1 (hLb j r k hq)).1
        simp only [Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul] at h
        linarith
      have hq0 : (0 : ℝ) ≤ ((gpt r k : ℝ≥0) : ℝ) := (gpt r k).2
      have hint : -(K1 * A) ≤
          ∫ u in (0 : ℝ)..((gpt r k : ℝ≥0) : ℝ), HL.hInt C i (X x u.toNNReal ω) := by
        have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
          (f := fun u => HL.hInt C i (X x u.toNNReal ω)) hq0
        have h2 : ∫ u in (0 : ℝ)..((gpt r k : ℝ≥0) : ℝ), |HL.hInt C i (X x u.toNNReal ω)| ≤
            ∫ u in (0 : ℝ)..(N : ℝ), |HL.hInt C i (X x u.toNNReal ω)| :=
          intervalIntegral.integral_mono_interval le_rfl hq0 hqr
            (ae_of_all _ fun u => abs_nonneg _) (hhc.abs.intervalIntegrable _ _)
        have h3 := neg_abs_le
          (∫ u in (0 : ℝ)..((gpt r k : ℝ≥0) : ℝ), HL.hInt C i (X x u.toNNReal ω))
        linarith
      have hxl : Real.log ε₂ < Real.log (x i) := Real.log_lt_log hε₂ hxi
      have hc0le : c0 ≤ Real.log (X x (gpt r k) ω i) := by
        rw [hlog, hc0]
        have hint' : -(K1 * A) ≤
            ∫ u in (0 : ℝ)..(gpt r k).val, HL.hInt C i (X x u.toNNReal ω) := hint
        linarith
      have he := Real.exp_le_exp.2 hc0le
      rw [Real.exp_log hfq] at he
      linarith
    have key := first_drop (fun t => X x t ω i) hfc hβ (N : ℝ≥0)
      (by show β < X x 0 ω i; rw [hx0]; linarith) hH
    show ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i
    intro t ht
    exact key t (by
      have : (t : ℝ) ≤ (N : ℝ) := ht.trans hTN
      exact_mod_cast this)
  have hSc : P Sᶜ ≤ ENNReal.ofReal (ε₁ / 2) := by
    refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add hPE0 ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun j _ => hPG j))).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hn0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (n : ℝ) * (ε₁ / (4 * (n + 1))) ≤ ε₁ / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  have h1 : (1 : ℝ≥0∞) ≤ P S + ENNReal.ofReal (ε₁ / 2) := by
    calc (1 : ℝ≥0∞) = P (S ∪ Sᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ P S + P Sᶜ := measure_union_le _ _
      _ ≤ P S + ENNReal.ofReal (ε₁ / 2) := by gcongr
  have h2 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨measure_ne_top P S, ENNReal.ofReal_ne_top⟩) h1
  rw [ENNReal.toReal_add (measure_ne_top P S) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_one] at h2
  linarith

end StochKolmogorov.Classify.STP

end FlatM_T1b
-- ===== T1full =====
section FlatM_T1full

/-! T1 `sink_box_avoids_far_set` (a17b7893 s4) assembled: `SB.sink_box` over T1a
(`GE.grid_escape_bound`), T1b (`STP.short_time_positivity`) and orthant invariance. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace StochKolmogorov.Classify.SBF
open StochKolmogorov.Classify EthierKurtz ItoLib

variable {n : ℕ}

end StochKolmogorov.Classify.SBF

end FlatM_T1full
-- ===== LogCont =====
section FlatM_LogCont

/-! NEW child `log_lln_continuous` (a17b7893 s2): the continuous-time strong law for `ln Xᵢ`
(Hening-Nguyen 1704.06984, (5.35) / proof of Lemma 5.9 p. 27, and (5.23) with Itô's formula).
`Yₖ(t) = ln Xₖ(t) − ln xₖ − ∫₀ᵗ hₖ(X)` is a continuous modification of `∑ⱼ ∫ gₖ(X)Γⱼₖ dBⱼ`
(`HL.log_rep`); the martingale strong law `ItoLib.G73.slln_Y` gives `Yₖ(t)/t → 0`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.LC

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

end StochKolmogorov.Classify.LC

end FlatM_LogCont
-- ===== K1a =====
section FlatM_K1a

/-! K1a of theorem_1_3 (8f909832): an ergodic invariant measure is concentrated on the interior of its
own face. Pure measure theory from face invariance (Extinct.lemma_3_1 clause 2 / Persist
kolmogorov_sde_face_invariance): open faces `F I` partition the orthant and are forward invariant, so
`μ|F I` (normalised) is invariant; extremality forces `μ (F I) ∈ {0,1}`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.K1a

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

/-- The open face whose positive coordinates are exactly `I`. -/
def F (I : Finset (Fin n)) : Set (SDEState n) := {x | x ∈ orthant n ∧ ∀ i, i ∈ I ↔ 0 < x i}

variable {Ω : Type*} [MeasurableSpace Ω]

end StochKolmogorov.Classify.K1a

end FlatM_K1a
-- ===== ErgSing =====
section FlatM_ErgSing

/-! Uniqueness core for K1b / K2b of theorem_1_3 (8f909832), pure measure theory:
* `dichotomy`: two ergodic invariant measures are equal or mutually singular (Hahn decomposition;
  `(μ-ν)⁺` is super-invariant, hence invariant, hence a multiple of `μ` by extremality). No
  measurability of `x ↦ trans t x A` is used (only superadditivity of the lower integral).
* `eq_of_overlap`: two ergodic measures charging a common set `K` on which the transition laws
  overlap (`ε ≤ P_t(x,A) + P_t(y,Aᶜ)`) are equal. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.ErgSing

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

end StochKolmogorov.Classify.ErgSing

end FlatM_ErgSing
-- ===== K1 =====
section FlatM_K1

/-! K1 of theorem_1_3 (8f909832): `M` is finite, modulo the analytic child `FaceOverlap` (TV overlap of
the transition laws on compact boxes inside each open face). K1b: two ergodic measures with the same
support are equal (both live on the same open face by K1a; they charge a common face box; overlap). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.K1

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

end StochKolmogorov.Classify.K1

end FlatM_K1
-- ===== KinvConv =====
section FlatM_KinvConv

/-! K2b of theorem_1_3 (8f909832): an invariant probability measure with no mass on the open orthant
lies in `Conv(M)` (finite convex combination of boundary ergodic measures). Per open face `F I`
(`I ≠ univ`): two invariant probabilities living on `F I` are equal (Hahn split into singular
invariant parts + TV overlap on a face box), so the normalized restriction of `π` to `F I` is ergodic. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.KinvConv

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing StochKolmogorov.Classify.K1

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

end StochKolmogorov.Classify.KinvConv

end FlatM_KinvConv
-- ===== T2 =====
section FlatM_T2

/-! T2 of lemma_5_9 (a17b7893): there are `R` and `η > 0` such that every invariant probability `π`
with no mass on the open far set `O(R,η) = {y | l1 y < R ∧ ∃ i ∉ supp μ, η < y i}` lies in
`Conv(M_μ ∪ {μ})`. Per open face `F I` with `I ⊄ supp μ` the invariant probability living on `F I`
(unique by the TV overlap) charges some `O(R_I, η_I)`; take `R = ∑ |R_I|`, `η = (∑ η_I⁻¹)⁻¹`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.L59

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing StochKolmogorov.Classify.K1 StochKolmogorov.Classify.KinvConv

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

end StochKolmogorov.Classify.L59

end FlatM_T2
-- ===== Glue =====
section FlatM_Glue

/-! Glue of lemma_5_9 (a17b7893): the conclusion from lemma_5_7 (invariance of limit points),
lemma_5_8, the new child T1 (the path started in `K^{k,Δ}_μ` avoids the open far set with
probability `> 1 - ε`), the new child T3 (on `U(ω) = {μ}` the log rates are `λᵢ(μ)`) and T2. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.L59

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing StochKolmogorov.Classify.K1

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

end StochKolmogorov.Classify.L59

end FlatM_Glue
-- ===== UcGlue =====
section FlatM_UcGlue

/-! U-c of 8f909832 (paper p.28, "similar to Lemma 5.8"): a.s. no limit point of the occupation
measures lies in `Conv(M²)`. Formal Assumption 1.5 is pointwise (`∃ i, λᵢ(ν) > 0` on `Conv(M²)`),
so no minimax is needed: it suffices that `λᵢ(π) ≤ 0` for every `π ∈ U(ω)` and every `i`.
`lyap_nonpos` derives that from Lemma 5.6 (sibling), Lemma 5.4 clause 1 (sibling), Lemma 5.7
clause 2 (sibling) and two pathwise facts along INTEGER times (hB) and SQUARES (hL):
 hL: `ln Xᵢ(m²)/m² − ∫ hᵢ dΠ̃_{m²} → 0` (Itô for ln Xᵢ + L² martingale bound + Borel–Cantelli), and
 hB: `ln Xᵢ(N) ≤ εN` eventually (moment bound + Borel–Cantelli).
The limit sequence `t_k` is replaced by `⌊√t_k⌋²` (`occ_close`, `tendsto_sq`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.UcGlue

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.UcGlue

end FlatM_UcGlue
-- ===== Dfam =====
section FlatM_Dfam

/-! K2-Γ (8f909832): a countable convergence-determining family `hD s k` of bounded continuous
functions on a separable metric space: tents `min 1 ((k+1) · infDist x (U s)ᶜ)` on finite unions
`U s` of balls from a countable basis. If `∫ hD s k dμᵢ → ∫ hD s k dμ` for every `s, k`, then
`μᵢ → μ` weakly (portmanteau, liminf over open sets). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StochKolmogorov.Classify.Dfam

variable {E : Type*} [MetricSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]

variable [MeasurableSpace E] [BorelSpace E]

end StochKolmogorov.Classify.Dfam

end FlatM_Dfam
-- ===== LimOcc =====
section FlatM_LimOcc

/-! K2-Γ (8f909832): occupation measures of a continuous path.
* `limitSet_eq_of_avg`: if the `Dfam.hD` averages of `occ X x T ω` converge to those of a probability
  measure `μ`, then `limitSet X x ω = {μ}` (portmanteau through the countable family).
* `avg_of_limitSet`: if `limitSet X x ω = {μ}` and `{occ X x t ω, t ≥ 1}` is tight (Lemma 5.7), then
  `∫ h d(occ X x T ω) → ∫ h dμ` for every bounded continuous `h` (Prokhorov). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.LimOcc

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.LimOcc

end FlatM_LimOcc
-- ===== HLglue =====
section FlatM_HLglue

/-! s13: parent-side glue for `hL`. The NEW child `log_lln_squares` (statement `LogLLNSq` below:
linear growth of `∫₀ᵗ gᵢ²` ⇒ `ln Xᵢ(m²)/m² − (1/m²)∫₀^{m²} hᵢ(X) → 0` a.s.) gives `hL` of
`UcGlue.lyap_nonpos` once `∫₀ᵗ gᵢ²` is bounded by lemma 5.4 clause 1 and the time average is
rewritten as an occupation integral. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.HLglue

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.HLglue

end FlatM_HLglue
-- ===== T3glue =====
section FlatM_T3glue

/-! T3 of lemma_5_9 (a17b7893): `ln Xᵢ(t)/t → λᵢ(μ)` (continuous time) on `{U(ω) = {μ}}`, from
* `LogLLNCont` (the NEW child `log_lln_continuous`: continuous-time strong law for `ln Xᵢ`,
  `ln Xᵢ(t)/t − t⁻¹∫₀ᵗ hᵢ(X) → 0` a.s. under a linear bound on `∫₀ᵗ gᵢ²`),
* lemma 5.4 cl. 1 (linear growth of `∫ growthWeight`), lemma 5.6 (uniform integrability along
  any sequence with weak convergence), lemma 5.7 (tightness of the occupation measures),
* `LimOcc.avg_of_limitSet` (`U = {μ}` + tight ⇒ `occ_T → μ` weakly, continuous `T`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.L59T3

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.L59T3

end FlatM_T3glue

open MeasureTheory ProbabilityTheory Filter EthierKurtz StochKolmogorov.Classify in
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction in
theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ R T : ℝ, 0 < T → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → ∃ β : ℝ, 0 < β ∧
      ∀ i, ∀ x ∈ orthant n, l1 x ≤ R → ε₂ < x i →
        1 - ε₁ < (P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i}).toReal := by
  exact StochKolmogorov.Classify.STP.short_time_positivity P C B X hX c γb hA
