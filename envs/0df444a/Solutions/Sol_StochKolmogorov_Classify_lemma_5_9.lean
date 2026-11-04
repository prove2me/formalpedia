-- Prove2me | solution 1 for StochKolmogorov.Classify.lemma_5_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T20:14:31.944042+00:00
-- url     : https://prove2.me/submissions/609f4fce-de75-45d2-b717-1d2a0df4b8cd

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Theorems.Thm_StochKolmogorov_Extinct_lemma_3_1
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_4
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_6
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_7
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_8
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_face_box_tv_overlap
import Theorems.Thm_StochKolmogorov_Classify_sink_box_avoids_far_set
import Theorems.Thm_StochKolmogorov_Classify_log_lln_continuous

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
variable {n : ℕ}

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

/-- The same coefficients, read as `Extinct` coefficients. -/
def ec (C : Coeffs n) : StochKolmogorov.Extinct.Coeffs n := ⟨C.f, C.g, C.Γ⟩

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

/-- Extinct's `δ₀` must also be `< 1`; shrinking `δ₀` keeps (3.2). -/
theorem delta_small (C : Coeffs n) {γb δ₀ : ℝ} (h : IsDelta0 C γb δ₀) :
    StochKolmogorov.Extinct.IsDelta0 (ec C) γb (min δ₀ (1 / 2)) := by
  refine ⟨lt_min h.1 (by norm_num), lt_min (lt_of_le_of_lt (min_le_left _ _) h.2.1)
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num)), fun x hx => ?_⟩
  show 3 * min δ₀ (1 / 2) * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
      + min δ₀ (1 / 2) * ∑ i, C.g i x ^ 2 ≤ γb * ∑ i, C.g i x ^ 2
  have hS1 : 0 ≤ ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hS2 : 0 ≤ ∑ i, C.g i x ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm : min δ₀ (1 / 2) ≤ δ₀ := min_le_left _ _
  have h3 := h.2.2 x hx
  have e1 := mul_le_mul_of_nonneg_right hm hS1
  have e2 := mul_le_mul_of_nonneg_right hm hS2
  linarith

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

end M10h

section M10i
open StochKolmogorov.Persist
variable {n : ℕ}

end M10i

section M10j
open StochKolmogorov.Persist
variable {n : ℕ}

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

theorem coord_meas {Ω : Type*} {m : MeasurableSpace Ω} {f : Ω → SDEState n}
    (hf : Measurable[m] f) (i : Fin n) : Measurable[m] (fun ω => f ω i) :=
  ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).measurable.comp hf

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

end StochKolmogorov.Classify.HL

end Part0


section Part1
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

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

variable {n : ℕ}

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

theorem coord_meas (i : Fin n) : Measurable fun x : SDEState n => x i :=
  (PiLp.continuous_apply 2 _ i).measurable

theorem measurableSet_orthant : MeasurableSet (orthant n) := by
  have e : orthant n = ⋂ i, {x : SDEState n | 0 ≤ x i} := by
    ext x; simp [orthant]
  rw [e]; exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (coord_meas i)

theorem measurableSet_F (I : Finset (Fin n)) : MeasurableSet (F I) := by
  have e : F I = orthant n ∩ ⋂ i, {x : SDEState n | i ∈ I ↔ 0 < x i} := by
    ext x; simp [F]
  rw [e]
  refine measurableSet_orthant.inter (MeasurableSet.iInter fun i => ?_)
  by_cases hi : i ∈ I
  · simp only [hi, true_iff]; exact measurableSet_lt measurable_const (coord_meas i)
  · simp only [hi, false_iff, not_lt]; exact measurableSet_le (coord_meas i) measurable_const

/-- The positive coordinates of a point. -/
noncomputable def pos (x : SDEState n) : Finset (Fin n) := Finset.univ.filter fun i => 0 < x i

theorem mem_F_pos {x : SDEState n} (hx : x ∈ orthant n) : x ∈ F (pos x) :=
  ⟨hx, fun i => by simp [pos]⟩

theorem F_unique {x : SDEState n} {I J : Finset (Fin n)} (hI : x ∈ F I) (hJ : x ∈ F J) : I = J := by
  ext i; rw [hI.2 i, hJ.2 i]

theorem orthant_subset : orthant n ⊆ ⋃ I : Finset (Fin n), F I :=
  fun x hx => Set.mem_iUnion.2 ⟨pos x, mem_F_pos hx⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Face invariance at fixed times, in the `F I` form. -/
def FaceInv (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ F I → ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ F I

/-- The clause-2 form of `Extinct.lemma_3_1` gives `FaceInv`. -/
theorem faceInv_of_clause {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (h : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0)) :
    FaceInv P X := by
  intro I x hx t
  filter_upwards [h I x hx.1 hx.2] with ω hω
  obtain ⟨h1, h2⟩ := hω t
  refine ⟨fun i => ?_, fun i => ⟨fun hi => h1 i hi, fun hp => ?_⟩⟩
  · by_cases hi : i ∈ I
    · exact (h1 i hi).le
    · exact (h2 i hi).ge
  · by_contra hi
    rw [h2 i hi] at hp
    exact lt_irrefl _ hp

theorem trans_null {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n} {t : ℝ≥0}
    {x : SDEState n} {S : Set (SDEState n)} (hS : MeasurableSet S)
    (h : ∀ᵐ ω ∂P, X x t ω ∉ S) : StochKolmogorov.Classify.trans P X t x S = 0 := by
  unfold StochKolmogorov.Classify.trans
  by_cases hm : AEMeasurable (X x t) P
  · rw [Measure.map_apply₀ hm hS.nullMeasurableSet]
    rw [ae_iff] at h
    convert h using 2
    ext ω; simp
  · rw [Measure.map_of_not_aemeasurable hm]; simp

theorem le_of_sum {a b c d : ℝ≥0∞} (hac : a ≤ c) (hbd : b ≤ d) (hc : c ≠ ∞) (hd : d ≠ ∞)
    (h : a + b = c + d) : a = c ∧ b = d := by
  refine ⟨le_antisymm hac ?_, le_antisymm hbd ?_⟩
  · have : c + d ≤ a + d := h ▸ add_le_add le_rfl hbd
    exact (ENNReal.add_le_add_iff_right hd).1 this
  · have : c + d ≤ c + b := h ▸ add_le_add hac le_rfl
    exact (ENNReal.add_le_add_iff_left hc).1 this

/-- Step A: the invariance relation splits along every open face. -/
theorem restrict_rel {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hface : FaceInv P X) {μ : Measure (SDEState n)} [IsFiniteMeasure μ]
    (horth : μ (orthant n)ᶜ = 0)
    (hinv : ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂μ = μ A)
    (I : Finset (Fin n)) (t : ℝ≥0) (A : Set (SDEState n)) (hA : MeasurableSet A) :
    ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x A ∂μ = μ (A ∩ F I) ∧
      ∫⁻ x in (F I)ᶜ, StochKolmogorov.Classify.trans P X t x A ∂μ = μ (A ∩ (F I)ᶜ) := by
  have hF := measurableSet_F I
  have k1 : ∀ x ∈ F I, StochKolmogorov.Classify.trans P X t x (F I)ᶜ = 0 := by
    intro x hx
    refine trans_null hF.compl ?_
    filter_upwards [hface I x hx t] with ω hω
    simpa using hω
  have k2 : ∀ x ∈ orthant n, x ∉ F I → StochKolmogorov.Classify.trans P X t x (F I) = 0 := by
    intro x hx hxI
    have hxJ := mem_F_pos hx
    refine trans_null hF ?_
    filter_upwards [hface _ x hxJ t] with ω hω hωI
    have e := F_unique hω hωI
    exact hxI (e ▸ hxJ)
  have hao : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact horth
  have e1 : ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x A ∂μ ≤ μ (A ∩ F I) := by
    calc ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x A ∂μ
        = ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x (A ∩ F I) ∂μ := by
          refine lintegral_congr_ae ((ae_restrict_iff' hF).2 (ae_of_all _ fun x hx => ?_))
          exact (measure_inter_conull (k1 x hx)).symm
      _ ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x (A ∩ F I) ∂μ :=
          setLIntegral_le_lintegral _ _
      _ = μ (A ∩ F I) := hinv t _ (hA.inter hF)
  have e2 : ∫⁻ x in (F I)ᶜ, StochKolmogorov.Classify.trans P X t x A ∂μ ≤ μ (A ∩ (F I)ᶜ) := by
    calc ∫⁻ x in (F I)ᶜ, StochKolmogorov.Classify.trans P X t x A ∂μ
        = ∫⁻ x in (F I)ᶜ, StochKolmogorov.Classify.trans P X t x (A ∩ (F I)ᶜ) ∂μ := by
          refine lintegral_congr_ae ((ae_restrict_iff' hF.compl).2 ?_)
          filter_upwards [hao] with x hx hxc
          refine (measure_inter_conull ?_).symm
          rw [compl_compl]; exact k2 x hx hxc
      _ ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x (A ∩ (F I)ᶜ) ∂μ :=
          setLIntegral_le_lintegral _ _
      _ = μ (A ∩ (F I)ᶜ) := hinv t _ (hA.inter hF.compl)
  refine le_of_sum e1 e2 (measure_ne_top _ _) (measure_ne_top _ _) ?_
  rw [lintegral_add_compl _ hF, hinv t A hA, ← Set.diff_eq, measure_inter_add_diff A hF]

/-- A normalised restriction satisfying the split relation is invariant. -/
theorem inv_restrict {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    {μ : Measure (SDEState n)} (horth : μ (orthant n)ᶜ = 0) {S : Set (SDEState n)}
    (hS : MeasurableSet S) {c : ℝ≥0∞} (hc : c = μ S) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hrel : ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      ∫⁻ x in S, StochKolmogorov.Classify.trans P X t x A ∂μ = μ (A ∩ S)) :
    IsInvariant P X (c⁻¹ • μ.restrict S) := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, ← hc,
      smul_eq_mul, ENNReal.inv_mul_cancel hc0 hct]
  · rw [Measure.smul_apply, Measure.restrict_apply' hS,
      measure_mono_null Set.inter_subset_left horth, smul_eq_mul, mul_zero]
  · intro t A hA
    rw [lintegral_smul_measure, hrel t A hA, Measure.smul_apply, Measure.restrict_apply hA,
      smul_eq_mul]

/-- Step B: an ergodic measure gives each open face mass `0` or `1`. -/
theorem face_zero_or_one {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hface : FaceInv P X) {μ : Measure (SDEState n)} (hE : IsErgodic P X μ)
    (I : Finset (Fin n)) : μ (F I) = 0 ∨ μ (F I) = 1 := by
  obtain ⟨⟨hprob, horth, hinv⟩, hext⟩ := hE
  haveI := hprob
  have hF := measurableSet_F I
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h1⟩ := hcon
  set a : ℝ≥0 := (μ (F I)).toNNReal with ha_def
  have ha : (a : ℝ≥0∞) = μ (F I) := ENNReal.coe_toNNReal (measure_ne_top _ _)
  have hlt : μ (F I) < 1 := lt_of_le_of_ne prob_le_one h1
  have ha0 : 0 < a := ENNReal.toNNReal_pos h0 (measure_ne_top _ _)
  have ha1 : a < 1 := by
    have : (a : ℝ≥0∞) < 1 := by rw [ha]; exact hlt
    exact_mod_cast this
  have hb : ((1 - a : ℝ≥0) : ℝ≥0∞) = μ (F I)ᶜ := by
    rw [prob_compl_eq_one_sub hF, ← ha, ENNReal.coe_sub, ENNReal.coe_one]
  have hb0 : ((1 - a : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [hb, prob_compl_eq_one_sub hF]; exact (tsub_pos_of_lt hlt).ne'
  have ha0' : (a : ℝ≥0∞) ≠ 0 := by rw [ha]; exact h0
  have hrel := restrict_rel hface horth hinv I
  have inv1 : IsInvariant P X ((a : ℝ≥0∞)⁻¹ • μ.restrict (F I)) :=
    inv_restrict horth hF ha ha0' ENNReal.coe_ne_top fun t A hA => (hrel t A hA).1
  have inv2 : IsInvariant P X (((1 - a : ℝ≥0) : ℝ≥0∞)⁻¹ • μ.restrict (F I)ᶜ) :=
    inv_restrict horth hF.compl hb hb0 ENNReal.coe_ne_top fun t A hA => (hrel t A hA).2
  have hdec : μ = (a : ℝ≥0∞) • ((a : ℝ≥0∞)⁻¹ • μ.restrict (F I)) +
      ((1 - a : ℝ≥0) : ℝ≥0∞) • (((1 - a : ℝ≥0) : ℝ≥0∞)⁻¹ • μ.restrict (F I)ᶜ) := by
    rw [smul_smul, smul_smul, ENNReal.mul_inv_cancel ha0' ENNReal.coe_ne_top,
      ENNReal.mul_inv_cancel hb0 ENNReal.coe_ne_top, one_smul, one_smul,
      Measure.restrict_add_restrict_compl hF]
  have heq := hext _ _ inv1 inv2 a ha0 ha1 hdec
  have hc := congrArg (fun m : Measure (SDEState n) => m (F I)ᶜ) heq
  simp only [Measure.smul_apply, Measure.restrict_apply hF.compl, Set.compl_inter_self,
    measure_empty, smul_eq_mul, mul_zero] at hc
  rw [← hb] at hc
  exact hb0 hc.symm

/-- K1a: an ergodic invariant measure is concentrated on `faceInt μ`. -/
theorem concentrates {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hface : FaceInv P X) {μ : Measure (SDEState n)} (hE : IsErgodic P X μ) :
    μ (faceInt μ)ᶜ = 0 := by
  have horth := hE.1.2.1
  haveI := hE.1.1
  have hcov : ∃ I, μ (F I) = 1 := by
    by_contra h
    push_neg at h
    have h0 : ∀ I, μ (F I) = 0 := fun I => (face_zero_or_one hface hE I).resolve_right (h I)
    have z : μ (orthant n) = 0 := measure_mono_null orthant_subset (measure_iUnion_null h0)
    have o : μ (orthant n) = 1 := (prob_compl_eq_zero_iff measurableSet_orthant).1 horth
    rw [z] at o
    exact zero_ne_one o
  obtain ⟨I, hI⟩ := hcov
  have hIc : μ (F I)ᶜ = 0 := (prob_compl_eq_zero_iff (measurableSet_F I)).2 hI
  have hsupp : supp μ = I := by
    ext i
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hi
      apply h
      refine measure_mono_null ?_ hIc
      intro x hx hxF
      exact hi ((hxF.2 i).2 hx)
    · intro hi h
      have hle : μ (F I) ≤ μ {x : SDEState n | 0 < x i} :=
        measure_mono fun x hx => (hx.2 i).1 hi
      rw [hI, h] at hle
      exact absurd hle (by norm_num)
  refine measure_mono_null ?_ hIc
  intro x hx hxF
  apply hx
  have hxo : ∀ i, 0 ≤ x i := hxF.1
  refine ⟨⟨hxF.1, fun i hi => ?_⟩, fun i hi => ?_⟩
  · rw [hsupp] at hi
    rcases (hxo i).lt_or_eq with h | h
    · exact absurd ((hxF.2 i).2 h) hi
    · exact h.symm
  · rw [hsupp] at hi
    exact (hxF.2 i).1 hi

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

/-- The setwise invariance relation. -/
def Rel (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) (m : Measure (SDEState n)) :
    Prop :=
  ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
    ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m = m A

/-- The transition laws from points of the orthant are probability measures. -/
def TotOne (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  ∀ x ∈ orthant n, ∀ t : ℝ≥0, StochKolmogorov.Classify.trans P X t x Set.univ = 1

theorem ge_of_sum {a b c d : ℝ≥0∞} (hca : c ≤ a) (hdb : d ≤ b) (hc : c ≠ ∞) (hd : d ≠ ∞)
    (h : a + b ≤ c + d) : a = c ∧ b = d := by
  refine ⟨le_antisymm ?_ hca, le_antisymm ?_ hdb⟩
  · have : a + d ≤ c + d := (add_le_add le_rfl hdb).trans h
    exact (ENNReal.add_le_add_iff_right hd).1 this
  · have : c + b ≤ c + d := (add_le_add hca le_rfl).trans h
    exact (ENNReal.add_le_add_iff_left hc).1 this

/-- A super-invariant finite measure on the orthant is invariant. -/
theorem super_to_rel (htot : TotOne P X) {m : Measure (SDEState n)} [IsFiniteMeasure m]
    (hm : m (orthant n)ᶜ = 0)
    (hsup : ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      m A ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m) : Rel P X m := by
  intro t A hA
  have hao : ∀ᵐ x ∂m, x ∈ orthant n := by rw [ae_iff]; exact hm
  have huniv : ∫⁻ x, StochKolmogorov.Classify.trans P X t x Set.univ ∂m = m Set.univ := by
    rw [← lintegral_one]
    refine lintegral_congr_ae ?_
    filter_upwards [hao] with x hx using htot x hx t
  have hle : ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m +
      ∫⁻ x, StochKolmogorov.Classify.trans P X t x Aᶜ ∂m ≤ m A + m Aᶜ := by
    calc _ ≤ ∫⁻ x, (StochKolmogorov.Classify.trans P X t x A +
            StochKolmogorov.Classify.trans P X t x Aᶜ) ∂m := le_lintegral_add _ _
      _ = ∫⁻ x, StochKolmogorov.Classify.trans P X t x Set.univ ∂m :=
          lintegral_congr fun x => measure_add_measure_compl hA
      _ = m Set.univ := huniv
      _ = m A + m Aᶜ := (measure_add_measure_compl hA).symm
  exact (ge_of_sum (hsup t A hA) (hsup t Aᶜ hA.compl) (measure_ne_top _ _)
    (measure_ne_top _ _) hle).1

/-- Super-invariance of the positive part, from a common remainder `w`. -/
theorem super_of_split {μ ν m m' w : Measure (SDEState n)} (hμi : Rel P X μ) (hνi : Rel P X ν)
    (hμ : μ = m + w) (hν : ν = m' + w) {H : Set (SDEState n)} (hHm : MeasurableSet H)
    (hmc : m Hᶜ = 0)
    (hmA : ∀ A, MeasurableSet A → A ⊆ H → m A ≤ μ A - ν A) :
    ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      m A ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m := by
  have core : ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      μ A ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m + ν A := by
    intro t A hA
    have e1 : ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m +
        ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂w = μ A := by
      rw [← lintegral_add_measure, ← hμ]; exact hμi t A hA
    have e2 : ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m' +
        ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂w = ν A := by
      rw [← lintegral_add_measure, ← hν]; exact hνi t A hA
    rw [← e1, ← e2]
    calc _ ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m +
          (∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m' +
            ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂w) :=
        add_le_add le_rfl le_add_self
      _ = _ := rfl
  intro t A hA
  have hH : m A = m (A ∩ H) := (measure_inter_conull hmc).symm
  rw [hH]
  calc m (A ∩ H) ≤ μ (A ∩ H) - ν (A ∩ H) := hmA _ (hA.inter hHm) Set.inter_subset_right
    _ ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x (A ∩ H) ∂m :=
        tsub_le_iff_right.2 (core t _ (hA.inter hHm))
    _ ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m :=
        lintegral_mono fun x => measure_mono Set.inter_subset_left

/-- Extremality applied to a split `μ = m + w` into two invariant parts. -/
theorem ergodic_split {μ m w : Measure (SDEState n)} (hE : IsErgodic P X μ)
    [IsFiniteMeasure m] [IsFiniteMeasure w] (hμ : μ = m + w) (hm : Rel P X m) (hw : Rel P X w)
    (h0 : 0 < m Set.univ) (h1 : m Set.univ < 1) : (m Set.univ)⁻¹ • m = μ := by
  obtain ⟨⟨hprob, horth, hinv⟩, hext⟩ := hE
  have hsum : w Set.univ + m Set.univ = 1 := by
    rw [add_comm, ← Measure.add_apply, ← hμ, measure_univ]
  have hw1 : w Set.univ = 1 - m Set.univ := ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) hsum
  set a : ℝ≥0 := (m Set.univ).toNNReal with ha_def
  have ha : (a : ℝ≥0∞) = m Set.univ := ENNReal.coe_toNNReal (measure_ne_top _ _)
  have ha0 : 0 < a := ENNReal.toNNReal_pos h0.ne' (measure_ne_top _ _)
  have ha1 : a < 1 := by
    have : (a : ℝ≥0∞) < 1 := by rw [ha]; exact h1
    exact_mod_cast this
  have hb : ((1 - a : ℝ≥0) : ℝ≥0∞) = w Set.univ := by
    rw [hw1, ← ha, ENNReal.coe_sub, ENNReal.coe_one]
  have hb0 : ((1 - a : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [hb, hw1]; exact (tsub_pos_of_lt h1).ne'
  have ha0' : (a : ℝ≥0∞) ≠ 0 := by rw [ha]; exact h0.ne'
  have hmo : m (orthant n)ᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc m (orthant n)ᶜ ≤ μ (orthant n)ᶜ := by rw [hμ, Measure.add_apply]; exact le_self_add
      _ = 0 := horth
  have hwo : w (orthant n)ᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc w (orthant n)ᶜ ≤ μ (orthant n)ᶜ := by rw [hμ, Measure.add_apply]; exact le_add_self
      _ = 0 := horth
  have inv1 : IsInvariant P X ((a : ℝ≥0∞)⁻¹ • m) := by
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul, ← ha, ENNReal.inv_mul_cancel ha0' ENNReal.coe_ne_top]
    · rw [Measure.smul_apply, hmo, smul_eq_mul, mul_zero]
    · intro t A hA
      rw [lintegral_smul_measure, hm t A hA, Measure.smul_apply, smul_eq_mul]
  have inv2 : IsInvariant P X (((1 - a : ℝ≥0) : ℝ≥0∞)⁻¹ • w) := by
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul, ← hb, ENNReal.inv_mul_cancel hb0 ENNReal.coe_ne_top]
    · rw [Measure.smul_apply, hwo, smul_eq_mul, mul_zero]
    · intro t A hA
      rw [lintegral_smul_measure, hw t A hA, Measure.smul_apply, smul_eq_mul]
  have hdec : μ = (a : ℝ≥0∞) • ((a : ℝ≥0∞)⁻¹ • m) +
      ((1 - a : ℝ≥0) : ℝ≥0∞) • (((1 - a : ℝ≥0) : ℝ≥0∞)⁻¹ • w) := by
    rw [smul_smul, smul_smul, ENNReal.mul_inv_cancel ha0' ENNReal.coe_ne_top,
      ENNReal.mul_inv_cancel hb0 ENNReal.coe_ne_top, one_smul, one_smul, hμ]
  have := hext _ _ inv1 inv2 a ha0 ha1 hdec
  rw [ha] at this
  exact this

/-- Two ergodic invariant measures are equal or mutually singular. -/
theorem dichotomy (htot : TotOne P X) {μ ν : Measure (SDEState n)} (hEμ : IsErgodic P X μ)
    (hEν : IsErgodic P X ν) :
    μ = ν ∨ ∃ H : Set (SDEState n), MeasurableSet H ∧ μ Hᶜ = 0 ∧ ν H = 0 := by
  haveI := hEμ.1.1
  haveI := hEν.1.1
  have hμi : Rel P X μ := hEμ.1.2.2
  have hνi : Rel P X ν := hEν.1.2.2
  obtain ⟨H, hH, hle, hge⟩ := hahn_decomposition μ ν
  have l1 : ν.restrict H ≤ μ.restrict H := by
    rw [Measure.le_iff]; intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hle _ (hs.inter hH) Set.inter_subset_right
  have l2 : μ.restrict Hᶜ ≤ ν.restrict Hᶜ := by
    rw [Measure.le_iff]; intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hge _ (hs.inter hH.compl) Set.inter_subset_right
  set m := μ.restrict H - ν.restrict H with hm_def
  set m' := ν.restrict Hᶜ - μ.restrict Hᶜ with hm'_def
  set w := ν.restrict H + μ.restrict Hᶜ with hw_def
  have hμ : μ = m + w := by
    calc μ = μ.restrict H + μ.restrict Hᶜ := (Measure.restrict_add_restrict_compl hH).symm
      _ = (m + ν.restrict H) + μ.restrict Hᶜ := by rw [Measure.sub_add_cancel_of_le l1]
      _ = m + w := by rw [add_assoc]
  have hν : ν = m' + w := by
    calc ν = ν.restrict H + ν.restrict Hᶜ := (Measure.restrict_add_restrict_compl hH).symm
      _ = ν.restrict H + (m' + μ.restrict Hᶜ) := by rw [Measure.sub_add_cancel_of_le l2]
      _ = m' + w := by rw [add_left_comm]
  have mle : m ≤ μ := hμ ▸ Measure.le_add_right le_rfl
  have m'le : m' ≤ ν := hν ▸ Measure.le_add_right le_rfl
  have wle : w ≤ μ := hμ ▸ Measure.le_add_left le_rfl
  haveI : IsFiniteMeasure m := isFiniteMeasure_of_le μ mle
  haveI : IsFiniteMeasure m' := isFiniteMeasure_of_le ν m'le
  haveI : IsFiniteMeasure w := isFiniteMeasure_of_le μ wle
  have hmc : m Hᶜ = 0 := by
    rw [hm_def, Measure.sub_apply hH.compl l1, Measure.restrict_apply hH.compl,
      Set.compl_inter_self, measure_empty, zero_tsub]
  have hm'c : m' Hᶜᶜ = 0 := by
    rw [hm'_def, Measure.sub_apply hH.compl.compl l2, Measure.restrict_apply hH.compl.compl,
      Set.compl_inter_self, measure_empty, zero_tsub]
  have hmA : ∀ A, MeasurableSet A → A ⊆ H → m A ≤ μ A - ν A := by
    intro A hA hAH
    rw [hm_def, Measure.sub_apply hA l1, Measure.restrict_apply hA, Measure.restrict_apply hA,
      Set.inter_eq_left.2 hAH]
  have hm'A : ∀ A, MeasurableSet A → A ⊆ Hᶜ → m' A ≤ ν A - μ A := by
    intro A hA hAH
    rw [hm'_def, Measure.sub_apply hA l2, Measure.restrict_apply hA, Measure.restrict_apply hA,
      Set.inter_eq_left.2 hAH]
  have orth_of_le : ∀ q : Measure (SDEState n), q ≤ μ → q (orthant n)ᶜ = 0 := fun q hq =>
    le_antisymm ((Measure.le_iff'.1 hq _).trans_eq hEμ.1.2.1) zero_le
  have orth_of_le' : ∀ q : Measure (SDEState n), q ≤ ν → q (orthant n)ᶜ = 0 := fun q hq =>
    le_antisymm ((Measure.le_iff'.1 hq _).trans_eq hEν.1.2.1) zero_le
  have hmR : Rel P X m :=
    super_to_rel htot (orth_of_le m mle) (super_of_split hμi hνi hμ hν hH hmc hmA)
  have hm'R : Rel P X m' :=
    super_to_rel htot (orth_of_le' m' m'le) (super_of_split hνi hμi hν hμ hH.compl hm'c hm'A)
  have hwR : Rel P X w := by
    intro t A hA
    have e1 : ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m +
        ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂w = m A + w A := by
      rw [← lintegral_add_measure, ← Measure.add_apply, ← hμ]; exact hμi t A hA
    rw [hmR t A hA] at e1
    exact (ENNReal.add_right_inj (measure_ne_top m A)).1 e1
  have hsμ : m Set.univ + w Set.univ = 1 := by rw [← Measure.add_apply, ← hμ, measure_univ]
  have hsν : m' Set.univ + w Set.univ = 1 := by rw [← Measure.add_apply, ← hν, measure_univ]
  have hcc : m Set.univ = m' Set.univ :=
    (ENNReal.add_left_inj (measure_ne_top w _)).1 (hsμ.trans hsν.symm)
  have hc1 : m Set.univ ≤ 1 := hsμ ▸ le_self_add
  rcases eq_or_lt_of_le (zero_le : (0:ℝ≥0∞) ≤ m Set.univ) with h0 | h0
  · left
    have z1 : m = 0 := Measure.measure_univ_eq_zero.1 h0.symm
    have z2 : m' = 0 := Measure.measure_univ_eq_zero.1 (hcc ▸ h0.symm)
    rw [hμ, hν, z1, z2]
  rcases eq_or_lt_of_le hc1 with h1 | h1
  · right
    have hw0 : w = 0 := by
      refine Measure.measure_univ_eq_zero.1 ?_
      rw [h1] at hsμ
      have := hsμ
      rw [← add_zero (1 : ℝ≥0∞)] at this
      conv_rhs at this => rw [add_zero]
      exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 (by rw [add_zero]; exact hsμ)
    refine ⟨H, hH, ?_, ?_⟩
    · rw [hμ, hw0, add_zero]; exact hmc
    · rw [hν, hw0, add_zero, ← compl_compl H]; exact hm'c
  · exfalso
    have hs1 := ergodic_split hEμ hμ hmR hwR h0 h1
    have hs2 := ergodic_split hEν hν hm'R hwR (hcc ▸ h0) (hcc ▸ h1)
    have a1 : μ Hᶜ = 0 := by
      rw [← hs1, Measure.smul_apply, hmc, smul_eq_mul, mul_zero]
    have a2 : ν H = 0 := by
      rw [← hs2, Measure.smul_apply, ← compl_compl H, hm'c, smul_eq_mul, mul_zero]
    have hw0 : w Set.univ = 0 := by
      rw [hw_def, Measure.add_apply, Measure.restrict_apply MeasurableSet.univ,
        Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Set.univ_inter, a1, a2, add_zero]
    rw [hw0, add_zero] at hsμ
    exact (ne_of_lt h1) hsμ

/-- Two ergodic measures charging a common overlap set are equal. -/
theorem eq_of_overlap (htot : TotOne P X) {μ ν : Measure (SDEState n)} (hEμ : IsErgodic P X μ)
    (hEν : IsErgodic P X ν) {K : Set (SDEState n)} (hK : MeasurableSet K) (hμK : μ K ≠ 0)
    (hνK : ν K ≠ 0) (t : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hov : ∀ x ∈ K, ∀ y ∈ K, ∀ A : Set (SDEState n), MeasurableSet A →
      ε ≤ StochKolmogorov.Classify.trans P X t x A + StochKolmogorov.Classify.trans P X t y Aᶜ) :
    μ = ν := by
  rcases dichotomy htot hEμ hEν with h | ⟨H, hH, hμH, hνH⟩
  · exact h
  exfalso
  have hy : ∃ y ∈ K, StochKolmogorov.Classify.trans P X t y H < ε := by
    by_contra hc
    push_neg at hc
    have b1 : ε * ν K ≤ ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x H ∂ν := by
      rw [← setLIntegral_const]
      exact lintegral_mono_ae ((ae_restrict_iff' hK).2 (ae_of_all _ hc))
    have b2 : ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x H ∂ν ≤ 0 :=
      (setLIntegral_le_lintegral _ _).trans_eq ((hEν.1.2.2 t H hH).trans hνH)
    have := le_antisymm (b1.trans b2) zero_le
    rcases mul_eq_zero.1 this with h | h
    · exact hε.ne' h
    · exact hνK h
  obtain ⟨y, hyK, hy⟩ := hy
  have hδ : 0 < ε - StochKolmogorov.Classify.trans P X t y H := tsub_pos_of_lt hy
  have hx : ∀ x ∈ K, ε - StochKolmogorov.Classify.trans P X t y H ≤
      StochKolmogorov.Classify.trans P X t x Hᶜ := by
    intro x hx
    have := hov x hx y hyK Hᶜ hH.compl
    rw [compl_compl] at this
    exact tsub_le_iff_right.2 this
  have b1 : (ε - StochKolmogorov.Classify.trans P X t y H) * μ K ≤
      ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x Hᶜ ∂μ := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hK).2 (ae_of_all _ hx))
  have b2 : ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x Hᶜ ∂μ ≤ 0 :=
    (setLIntegral_le_lintegral _ _).trans_eq ((hEμ.1.2.2 t Hᶜ hH.compl).trans hμH)
  have := le_antisymm (b1.trans b2) zero_le
  rcases mul_eq_zero.1 this with h | h
  · exact hδ.ne' h
  · exact hμK h

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

theorem totOne_of_family {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hX : IsSolutionFamily P C B X) : TotOne P X := by
  intro x hx t
  haveI := hX.1
  unfold StochKolmogorov.Classify.trans
  rw [Measure.map_apply ((hX.2.2 x hx).1 t) MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- A compact box inside the open face `F S`. -/
def faceBox (S : Finset (Fin n)) (a b : ℝ) : Set (SDEState n) :=
  {x | x ∈ F S ∧ ∀ i ∈ S, a ≤ x i ∧ x i ≤ b}

theorem measurableSet_faceBox (S : Finset (Fin n)) (a b : ℝ) : MeasurableSet (faceBox S a b) := by
  have e : faceBox S a b = F S ∩ ⋂ i ∈ S, ({x : SDEState n | a ≤ x i} ∩ {x | x i ≤ b}) := by
    ext x; simp [faceBox]
  rw [e]
  exact (measurableSet_F S).inter (Finset.measurableSet_biInter S fun i _ =>
    (measurableSet_le measurable_const (coord_meas i)).inter
      (measurableSet_le (coord_meas i) measurable_const))

/-- The analytic child: TV overlap of `P_t(x,·)` and `P_t(y,·)` on each face box. -/
def FaceOverlap (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) (S : Finset (Fin n)) :
    Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ∃ (t : ℝ≥0) (ε : ℝ≥0∞), 0 < ε ∧
    ∀ x ∈ faceBox S a b, ∀ y ∈ faceBox S a b, ∀ A : Set (SDEState n), MeasurableSet A →
      ε ≤ StochKolmogorov.Classify.trans P X t x A + StochKolmogorov.Classify.trans P X t y Aᶜ

theorem mem_some_box {S : Finset (Fin n)} {x : SDEState n} (hx : x ∈ F S) :
    ∃ k : ℕ, x ∈ faceBox S ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1) := by
  have hi : ∀ i ∈ S, ∃ N : ℕ, ((N : ℝ) + 1)⁻¹ ≤ x i ∧ x i ≤ (N : ℝ) + 1 := by
    intro i hiS
    have hp : 0 < x i := (hx.2 i).1 hiS
    obtain ⟨N, hN⟩ := exists_nat_gt (max (x i) (x i)⁻¹)
    refine ⟨N, ?_, ?_⟩
    · have : (x i)⁻¹ < (N : ℝ) + 1 := by linarith [le_max_right (x i) (x i)⁻¹]
      exact (inv_lt_of_inv_lt₀ hp this).le
    · linarith [le_max_left (x i) (x i)⁻¹]
  choose! N hN using hi
  refine ⟨S.sup N, hx, fun i hiS => ?_⟩
  have hle : (N i : ℝ) + 1 ≤ ((S.sup N : ℕ) : ℝ) + 1 := by
    have : N i ≤ S.sup N := Finset.le_sup hiS
    have : (N i : ℝ) ≤ (S.sup N : ℕ) := by exact_mod_cast this
    linarith
  have hpos : (0 : ℝ) < (N i : ℝ) + 1 := by positivity
  refine ⟨le_trans (inv_anti₀ hpos hle) (hN i hiS).1, le_trans (hN i hiS).2 hle⟩

theorem faceBox_mono {S : Finset (Fin n)} {k k' : ℕ} (h : k ≤ k') :
    faceBox S ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1) ⊆ faceBox S ((k' : ℝ) + 1)⁻¹ ((k' : ℝ) + 1) := by
  intro x hx
  have hle : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by
    have : (k : ℝ) ≤ k' := by exact_mod_cast h
    linarith
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine ⟨hx.1, fun i hi => ⟨le_trans (inv_anti₀ hpos hle) (hx.2 i hi).1, le_trans (hx.2 i hi).2 hle⟩⟩

theorem faceInt_subset_F (μ : Measure (SDEState n)) : faceInt μ ⊆ F (supp μ) := by
  intro x hx
  refine ⟨hx.1.1, fun i => ⟨fun hi => hx.2 i hi, fun hp => ?_⟩⟩
  by_contra hi
  rw [hx.1.2 i hi] at hp
  exact lt_irrefl _ hp

theorem exists_box_pos {μ : Measure (SDEState n)} {S : Finset (Fin n)} (h : μ (F S) ≠ 0) :
    ∃ k : ℕ, μ (faceBox S ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hc)
  obtain ⟨k, hk⟩ := mem_some_box hx
  exact Set.mem_iUnion.2 ⟨k, hk⟩

/-- K1b: two ergodic measures with the same support are equal. -/
theorem eq_of_supp_eq (hface : FaceInv P X) (htot : TotOne P X)
    (hov : ∀ S : Finset (Fin n), S ≠ Finset.univ → FaceOverlap P X S) {μ ν : Measure (SDEState n)}
    (hEμ : IsErgodic P X μ) (hμo : μ (openOrthant n) = 0) (hEν : IsErgodic P X ν)
    (hs : supp μ = supp ν) : μ = ν := by
  haveI := hEμ.1.1
  haveI := hEν.1.1
  have hμF : μ (F (supp μ))ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.2 (faceInt_subset_F μ)) (concentrates hface hEμ)
  have hνF : ν (F (supp μ))ᶜ = 0 := by
    rw [hs]
    exact measure_mono_null (Set.compl_subset_compl.2 (faceInt_subset_F ν)) (concentrates hface hEν)
  have hμ1 : μ (F (supp μ)) ≠ 0 := by
    rw [(prob_compl_eq_zero_iff (measurableSet_F _)).1 hμF]; exact one_ne_zero
  have hν1 : ν (F (supp μ)) ≠ 0 := by
    rw [(prob_compl_eq_zero_iff (measurableSet_F _)).1 hνF]; exact one_ne_zero
  obtain ⟨k1, hk1⟩ := exists_box_pos hμ1
  obtain ⟨k2, hk2⟩ := exists_box_pos hν1
  have hpos : (0 : ℝ) < ((max k1 k2 : ℕ) : ℝ) + 1 := by positivity
  have hab : (((max k1 k2 : ℕ) : ℝ) + 1)⁻¹ ≤ ((max k1 k2 : ℕ) : ℝ) + 1 := by
    have h1 : (1 : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    exact le_trans (inv_le_one_of_one_le₀ h1) h1
  have hne : supp μ ≠ Finset.univ := by
    intro hu
    apply hμ1
    have hsub : F (supp μ) ⊆ openOrthant n := by
      intro x hx
      show ∀ i, 0 < x i
      intro i
      exact (hx.2 i).1 (hu ▸ Finset.mem_univ i)
    exact measure_mono_null hsub hμo
  obtain ⟨t, ε, hε, hov'⟩ := hov (supp μ) hne _ _ (inv_pos.2 hpos) hab
  refine eq_of_overlap htot hEμ hEν (measurableSet_faceBox _ _ _) ?_ ?_ t hε hov'
  · exact fun h => hk1 (measure_mono_null (faceBox_mono (le_max_left k1 k2)) h)
  · exact fun h => hk2 (measure_mono_null (faceBox_mono (le_max_right k1 k2)) h)

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

/-- Singular finite invariant measures cannot both charge an overlap set. -/
theorem false_of_overlap {m m' : Measure (SDEState n)} (hm : Rel P X m) (hm' : Rel P X m')
    {H : Set (SDEState n)} (hH : MeasurableSet H) (hmH : m Hᶜ = 0) (hm'H : m' H = 0)
    {K : Set (SDEState n)} (hK : MeasurableSet K) (hmK : m K ≠ 0) (hm'K : m' K ≠ 0)
    (t : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hov : ∀ x ∈ K, ∀ y ∈ K, ∀ A : Set (SDEState n), MeasurableSet A →
      ε ≤ StochKolmogorov.Classify.trans P X t x A + StochKolmogorov.Classify.trans P X t y Aᶜ) :
    False := by
  have hy : ∃ y ∈ K, StochKolmogorov.Classify.trans P X t y H < ε := by
    by_contra hc
    push_neg at hc
    have b1 : ε * m' K ≤ ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x H ∂m' := by
      rw [← setLIntegral_const]
      exact lintegral_mono_ae ((ae_restrict_iff' hK).2 (ae_of_all _ hc))
    have b2 : ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x H ∂m' ≤ 0 :=
      (setLIntegral_le_lintegral _ _).trans_eq ((hm' t H hH).trans hm'H)
    have := le_antisymm (b1.trans b2) zero_le
    rcases mul_eq_zero.1 this with h | h
    · exact hε.ne' h
    · exact hm'K h
  obtain ⟨y, hyK, hy⟩ := hy
  have hδ : 0 < ε - StochKolmogorov.Classify.trans P X t y H := tsub_pos_of_lt hy
  have hx : ∀ x ∈ K, ε - StochKolmogorov.Classify.trans P X t y H ≤
      StochKolmogorov.Classify.trans P X t x Hᶜ := by
    intro x hx
    have := hov x hx y hyK Hᶜ hH.compl
    rw [compl_compl] at this
    exact tsub_le_iff_right.2 this
  have b1 : (ε - StochKolmogorov.Classify.trans P X t y H) * m K ≤
      ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x Hᶜ ∂m := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hK).2 (ae_of_all _ hx))
  have b2 : ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x Hᶜ ∂m ≤ 0 :=
    (setLIntegral_le_lintegral _ _).trans_eq ((hm t Hᶜ hH.compl).trans hmH)
  have := le_antisymm (b1.trans b2) zero_le
  rcases mul_eq_zero.1 this with h | h
  · exact hδ.ne' h
  · exact hmK h

/-- Two invariant probabilities living on the open face `F I` are equal. -/
theorem inv_eq_of_face (htot : TotOne P X) {I : Finset (Fin n)} (hov : FaceOverlap P X I)
    {μ ν : Measure (SDEState n)} (hμI : IsInvariant P X μ) (hνI : IsInvariant P X ν)
    (hμF : μ (F I)ᶜ = 0) (hνF : ν (F I)ᶜ = 0) : μ = ν := by
  haveI := hμI.1
  haveI := hνI.1
  have hμi : Rel P X μ := hμI.2.2
  have hνi : Rel P X ν := hνI.2.2
  obtain ⟨H, hH, hle, hge⟩ := hahn_decomposition μ ν
  have l1 : ν.restrict H ≤ μ.restrict H := by
    rw [Measure.le_iff]; intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hle _ (hs.inter hH) Set.inter_subset_right
  have l2 : μ.restrict Hᶜ ≤ ν.restrict Hᶜ := by
    rw [Measure.le_iff]; intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hge _ (hs.inter hH.compl) Set.inter_subset_right
  set m := μ.restrict H - ν.restrict H with hm_def
  set m' := ν.restrict Hᶜ - μ.restrict Hᶜ with hm'_def
  set w := ν.restrict H + μ.restrict Hᶜ with hw_def
  have hμ : μ = m + w := by
    calc μ = μ.restrict H + μ.restrict Hᶜ := (Measure.restrict_add_restrict_compl hH).symm
      _ = (m + ν.restrict H) + μ.restrict Hᶜ := by rw [Measure.sub_add_cancel_of_le l1]
      _ = m + w := by rw [add_assoc]
  have hν : ν = m' + w := by
    calc ν = ν.restrict H + ν.restrict Hᶜ := (Measure.restrict_add_restrict_compl hH).symm
      _ = ν.restrict H + (m' + μ.restrict Hᶜ) := by rw [Measure.sub_add_cancel_of_le l2]
      _ = m' + w := by rw [add_left_comm]
  have mle : m ≤ μ := hμ ▸ Measure.le_add_right le_rfl
  have m'le : m' ≤ ν := hν ▸ Measure.le_add_right le_rfl
  haveI : IsFiniteMeasure m := isFiniteMeasure_of_le μ mle
  haveI : IsFiniteMeasure m' := isFiniteMeasure_of_le ν m'le
  have wle : w ≤ μ := hμ ▸ Measure.le_add_left le_rfl
  haveI : IsFiniteMeasure w := isFiniteMeasure_of_le μ wle
  have hmc : m Hᶜ = 0 := by
    rw [hm_def, Measure.sub_apply hH.compl l1, Measure.restrict_apply hH.compl,
      Set.compl_inter_self, measure_empty, zero_tsub]
  have hm'c : m' H = 0 := by
    rw [hm'_def, Measure.sub_apply hH l2, Measure.restrict_apply hH,
      Set.inter_compl_self, measure_empty, zero_tsub]
  have hmA : ∀ A, MeasurableSet A → A ⊆ H → m A ≤ μ A - ν A := by
    intro A hA hAH
    rw [hm_def, Measure.sub_apply hA l1, Measure.restrict_apply hA, Measure.restrict_apply hA,
      Set.inter_eq_left.2 hAH]
  have hm'A : ∀ A, MeasurableSet A → A ⊆ Hᶜ → m' A ≤ ν A - μ A := by
    intro A hA hAH
    rw [hm'_def, Measure.sub_apply hA l2, Measure.restrict_apply hA, Measure.restrict_apply hA,
      Set.inter_eq_left.2 hAH]
  have hm'cc : m' Hᶜᶜ = 0 := by rw [compl_compl]; exact hm'c
  have null_of_le : ∀ (q r : Measure (SDEState n)) (S : Set (SDEState n)), q ≤ r → r S = 0 →
      q S = 0 := fun q r S hq hr => le_antisymm ((Measure.le_iff'.1 hq _).trans_eq hr) zero_le
  have hmR : Rel P X m :=
    super_to_rel htot (null_of_le m μ _ mle hμI.2.1) (super_of_split hμi hνi hμ hν hH hmc hmA)
  have hm'R : Rel P X m' :=
    super_to_rel htot (null_of_le m' ν _ m'le hνI.2.1)
      (super_of_split hνi hμi hν hμ hH.compl hm'cc hm'A)
  have hsμ : m Set.univ + w Set.univ = 1 := by rw [← Measure.add_apply, ← hμ, measure_univ]
  have hsν : m' Set.univ + w Set.univ = 1 := by rw [← Measure.add_apply, ← hν, measure_univ]
  have hcc : m Set.univ = m' Set.univ :=
    (ENNReal.add_left_inj (measure_ne_top w _)).1 (hsμ.trans hsν.symm)
  by_cases h0 : m Set.univ = 0
  · have z1 : m = 0 := Measure.measure_univ_eq_zero.1 h0
    have z2 : m' = 0 := Measure.measure_univ_eq_zero.1 (hcc ▸ h0)
    rw [hμ, hν, z1, z2]
  exfalso
  have hmF : m (F I) ≠ 0 := by
    intro hz
    apply h0
    have := measure_union_le (μ := m) (F I) (F I)ᶜ
    rw [Set.union_compl_self, hz, null_of_le m μ _ mle hμF, add_zero] at this
    exact le_antisymm this zero_le
  have hm'F : m' (F I) ≠ 0 := by
    intro hz
    apply h0
    rw [hcc]
    have := measure_union_le (μ := m') (F I) (F I)ᶜ
    rw [Set.union_compl_self, hz, null_of_le m' ν _ m'le hνF, add_zero] at this
    exact le_antisymm this zero_le
  obtain ⟨k1, hk1⟩ := exists_box_pos hmF
  obtain ⟨k2, hk2⟩ := exists_box_pos hm'F
  set k := max k1 k2
  have hK := measurableSet_faceBox (n := n) I ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)
  have hmK : m (faceBox I ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)) ≠ 0 := fun hz =>
    hk1 (measure_mono_null (faceBox_mono (le_max_left k1 k2)) hz)
  have hm'K : m' (faceBox I ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)) ≠ 0 := fun hz =>
    hk2 (measure_mono_null (faceBox_mono (le_max_right k1 k2)) hz)
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hab : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    exact le_trans (inv_le_one_of_one_le₀ this) this
  obtain ⟨t, ε, hε, hovt⟩ := hov _ _ (inv_pos.2 hk0) hab
  exact false_of_overlap hmR hm'R hH hmc hm'c hK hmK hm'K t hε hovt

/-- An invariant probability living on the open face `F I` is ergodic. -/
theorem ergodic_of_face (htot : TotOne P X) {I : Finset (Fin n)} (hov : FaceOverlap P X I)
    {π : Measure (SDEState n)} (hπ : IsInvariant P X π) (hπF : π (F I)ᶜ = 0) :
    IsErgodic P X π := by
  refine ⟨hπ, fun ν₁ ν₂ h1 _ a ha _ he => ?_⟩
  refine inv_eq_of_face htot hov h1 hπ ?_ hπF
  have hle : (a : ℝ≥0∞) * ν₁ (F I)ᶜ ≤ π (F I)ᶜ := by
    rw [he, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact le_self_add
  rw [hπF] at hle
  have := le_antisymm hle zero_le
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (by exact_mod_cast ha.ne')
  · exact h

theorem F_disjoint {I J : Finset (Fin n)} (h : I ≠ J) : Disjoint (F I) (F J) :=
  Set.disjoint_left.2 fun _ hI hJ => h (F_unique hI hJ)

theorem orthant_eq_iUnion : orthant n = ⋃ I ∈ (Finset.univ : Finset (Finset (Fin n))), F I := by
  ext x
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
  exact ⟨fun hx => ⟨pos x, mem_F_pos hx⟩, fun ⟨_, h⟩ => h.1⟩

theorem F_univ_subset : F (Finset.univ : Finset (Fin n)) ⊆ openOrthant n :=
  fun _ hx i => (hx.2 i).1 (Finset.mem_univ i)

theorem openOrthant_null_of_ne {I : Finset (Fin n)} (hI : I ≠ Finset.univ)
    {x : SDEState n} (hx : x ∈ F I) : x ∉ openOrthant n := by
  intro ho
  apply hI
  ext i
  simp only [Finset.mem_univ, iff_true]
  exact (hx.2 i).2 (ho i)

/-- K2b: an invariant probability with no mass on the open orthant lies in `Conv(M)`. -/
theorem conv_of_inv (htot : TotOne P X) (hface : FaceInv P X)
    (hov : ∀ I : Finset (Fin n), I ≠ Finset.univ → FaceOverlap P X I)
    {π : Measure (SDEState n)} (hπ : IsInvariant P X π) (hπo : π (openOrthant n) = 0) :
    π ∈ conv (bdryErgodic P X) := by
  classical
  haveI := hπ.1
  set T := (Finset.univ : Finset (Finset (Fin n))).filter (fun I => π (F I) ≠ 0) with hT
  have hTne : ∀ I ∈ T, I ≠ Finset.univ := by
    intro I hI he
    rw [hT, Finset.mem_filter, he] at hI
    exact hI.2 (measure_mono_null F_univ_subset hπo)
  let g : Finset (Fin n) → Measure (SDEState n) := fun I => (π (F I))⁻¹ • π.restrict (F I)
  have hrelI : ∀ I, ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x A ∂π = π (A ∩ F I) :=
    fun I t A hA => (restrict_rel hface hπ.2.1 hπ.2.2 I t A hA).1
  have hgI : ∀ I ∈ T, IsInvariant P X (g I) := fun I hI =>
    inv_restrict hπ.2.1 (measurableSet_F I) rfl (Finset.mem_filter.1 hI).2 (measure_ne_top _ _)
      (hrelI I)
  have hgF : ∀ I, g I (F I)ᶜ = 0 := by
    intro I
    simp only [g, Measure.smul_apply, Measure.restrict_apply (measurableSet_F I).compl,
      Set.compl_inter_self, measure_empty, smul_eq_mul, mul_zero]
  have hgE : ∀ I ∈ T, g I ∈ bdryErgodic P X := by
    intro I hI
    refine ⟨ergodic_of_face htot (hov I (hTne I hI)) (hgI I hI) (hgF I), ?_⟩
    exact measure_mono_null (show openOrthant n ⊆ (F I)ᶜ from
      fun x hx hxF => openOrthant_null_of_ne (hTne I hI) hxF hx) (hgF I)
  have hgFI : ∀ I ∈ T, g I (F I) = 1 := by
    intro I hI
    have hc0 := (Finset.mem_filter.1 hI).2
    simp only [g, Measure.smul_apply, Measure.restrict_apply (measurableSet_F I), Set.inter_self,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel hc0 (measure_ne_top _ _)
  have hinj : ∀ I ∈ T, ∀ J ∈ T, g I = g J → I = J := by
    intro I hI J hJ he
    by_contra hne
    have h1 := hgFI I hI
    rw [he] at h1
    have : g J (F I) = 0 :=
      measure_mono_null (fun x hx hxJ => (F_disjoint hne).ne_of_mem hx hxJ rfl) (hgF J)
    rw [this] at h1
    exact zero_ne_one h1
  let w : Finset (Fin n) → ℝ≥0 := fun I => (π (F I)).toNNReal
  have hw : ∀ I, (w I : ℝ≥0∞) = π (F I) := fun I => ENNReal.coe_toNNReal (measure_ne_top _ _)
  let p : Measure (SDEState n) → ℝ≥0 := fun ν => ∑ I ∈ T, if g I = ν then w I else 0
  have hp : ∀ J ∈ T, p (g J) = w J := by
    intro J hJ
    simp only [p]
    rw [Finset.sum_eq_single J]
    · simp
    · intro I hI hIJ
      rw [if_neg (fun h => hIJ (hinj I hI J hJ h))]
    · intro h; exact absurd hJ h
  -- the face decomposition of `π`
  have hsum_sets : ∀ A : Set (SDEState n), MeasurableSet A →
      ∑ I ∈ T, π (A ∩ F I) = π A := by
    intro A hA
    have hall : ∑ I ∈ (Finset.univ : Finset (Finset (Fin n))), π (A ∩ F I) = π A := by
      rw [← measure_biUnion_finset]
      · rw [← Set.inter_iUnion₂, ← orthant_eq_iUnion]
        have := measure_inter_add_diff (μ := π) A (measurableSet_orthant (n := n))
        rw [show π (A \ orthant n) = 0 from measure_mono_null (Set.diff_subset_compl _ _) hπ.2.1,
          add_zero] at this
        exact this
      · intro I _ J _ hIJ
        exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right (F_disjoint hIJ)
      · intro I _; exact hA.inter (measurableSet_F I)
    rw [← hall, hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs with h
    · rfl
    · push_neg at h
      exact (measure_mono_null Set.inter_subset_right h).symm
  refine ⟨T.image g, p, ?_, ?_, ?_, ?_⟩
  · intro ν hν
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hν)
    exact hgE I hI
  · intro ν hν
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hν
    rw [hp I hI]
    exact ENNReal.toNNReal_pos (Finset.mem_filter.1 hI).2 (measure_ne_top _ _)
  · rw [Finset.sum_image hinj]
    rw [Finset.sum_congr rfl fun I hI => hp I hI]
    have h1 := hsum_sets Set.univ MeasurableSet.univ
    simp only [Set.univ_inter, measure_univ] at h1
    have : ((∑ I ∈ T, w I : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [ENNReal.coe_finset_sum]
      simp only [hw]
      exact h1
    exact_mod_cast this
  · rw [Finset.sum_image hinj]
    ext A hA
    rw [Measure.coe_finset_sum, Finset.sum_apply, ← hsum_sets A hA]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [hp I hI, hw I]
    simp only [g, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (Finset.mem_filter.1 hI).2 (measure_ne_top _ _),
      one_mul]

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

/-- The far set `O(R,η)`. -/
def farSet (μ : Measure (SDEState n)) (R η : ℝ) : Set (SDEState n) :=
  {y | l1 y < R ∧ ∃ i, i ∉ supp μ ∧ η < y i}

theorem farSet_mono (μ : Measure (SDEState n)) {R R' η η' : ℝ} (hR : R ≤ R') (hη : η' ≤ η) :
    farSet μ R η ⊆ farSet μ R' η' :=
  fun _ ⟨h1, i, hi, h2⟩ => ⟨h1.trans_le hR, i, hi, hη.trans_lt h2⟩

theorem face_charges (htot : TotOne P X) {I : Finset (Fin n)} (hov : FaceOverlap P X I)
    (μ : Measure (SDEState n)) (hI : ¬ I ⊆ supp μ) :
    ∃ R η : ℝ, 0 < η ∧ ∀ ν : Measure (SDEState n), IsInvariant P X ν → ν (F I)ᶜ = 0 →
      0 < ν (farSet μ R η) := by
  by_cases h : ∃ ν0 : Measure (SDEState n), IsInvariant P X ν0 ∧ ν0 (F I)ᶜ = 0
  · obtain ⟨ν0, h0, h0F⟩ := h
    obtain ⟨i, hiI, hiμ⟩ := Finset.not_subset.1 hI
    haveI := h0.1
    have hcov : F I ⊆ ⋃ m : ℕ, farSet μ (m : ℝ) ((m : ℝ) + 1)⁻¹ := by
      intro y hy
      have hyi : 0 < y i := (hy.2 i).1 hiI
      obtain ⟨m1, hm1⟩ := exists_nat_gt (l1 y)
      obtain ⟨m2, hm2⟩ := exists_nat_one_div_lt hyi
      refine Set.mem_iUnion.2 ⟨max m1 m2, ?_, i, hiμ, ?_⟩
      · exact hm1.trans_le (by exact_mod_cast le_max_left _ _)
      · have h2 : (m2 : ℝ) + 1 ≤ ((max m1 m2 : ℕ) : ℝ) + 1 := by
          have : (m2 : ℝ) ≤ ((max m1 m2 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
          linarith
        calc (((max m1 m2 : ℕ) : ℝ) + 1)⁻¹ ≤ ((m2 : ℝ) + 1)⁻¹ := inv_anti₀ (by positivity) h2
          _ = 1 / ((m2 : ℝ) + 1) := by rw [one_div]
          _ < y i := hm2
    have hF1 : ν0 (F I) ≠ 0 := by
      intro h0'
      have hu : ν0 Set.univ = 0 := by
        rw [← Set.union_compl_self (F I)]
        exact measure_union_null h0' h0F
      simp at hu
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ν0 (farSet μ (m : ℝ) ((m : ℝ) + 1)⁻¹) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hF1 (measure_mono_null hcov (measure_iUnion_null hc))
    refine ⟨m, ((m : ℝ) + 1)⁻¹, by positivity, fun ν hν hνF => ?_⟩
    have he : ν = ν0 := inv_eq_of_face htot hov hν h0 hνF h0F
    rw [he]
    exact pos_iff_ne_zero.2 hm
  · push_neg at h
    exact ⟨0, 1, one_pos, fun ν hν hνF => absurd hνF (h ν hν)⟩

/-- T2: invariant probabilities that do not charge the far set lie in `Conv(M_μ ∪ {μ})`. -/
theorem exists_far (htot : TotOne P X) (hface : FaceInv P X)
    (hov : ∀ I : Finset (Fin n), FaceOverlap P X I) {μ : Measure (SDEState n)}
    (hμ : μ ∈ bdryErgodic P X) :
    ∃ R η : ℝ, 0 < η ∧ ∀ π : Measure (SDEState n), IsInvariant P X π →
      π (farSet μ R η) = 0 → π ∈ conv (subErgodic P X μ ∪ {μ}) := by
  classical
  have hch : ∀ I : Finset (Fin n), ∃ R η : ℝ, 0 < η ∧ (¬ I ⊆ supp μ →
      ∀ ν : Measure (SDEState n), IsInvariant P X ν → ν (F I)ᶜ = 0 →
        0 < ν (farSet μ R η)) := by
    intro I
    by_cases hI : I ⊆ supp μ
    · exact ⟨0, 1, one_pos, fun h => absurd hI h⟩
    · obtain ⟨R, η, hη, h⟩ := face_charges htot (hov I) μ hI
      exact ⟨R, η, hη, fun _ => h⟩
  choose Rf ηf hηf hRη using hch
  have hsum_pos : 0 < ∑ I : Finset (Fin n), (ηf I)⁻¹ :=
    Finset.sum_pos (fun I _ => inv_pos.2 (hηf I)) Finset.univ_nonempty
  have hRle : ∀ I, Rf I ≤ ∑ J : Finset (Fin n), |Rf J| := fun I =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun J => |Rf J|)
      (fun J _ => abs_nonneg _) (Finset.mem_univ I))
  have hηle : ∀ I, (∑ J : Finset (Fin n), (ηf J)⁻¹)⁻¹ ≤ ηf I := fun I => by
    have h1 : (ηf I)⁻¹ ≤ ∑ J : Finset (Fin n), (ηf J)⁻¹ :=
      Finset.single_le_sum (f := fun J => (ηf J)⁻¹) (fun J _ => (inv_pos.2 (hηf J)).le)
        (Finset.mem_univ I)
    have h2 := inv_anti₀ (inv_pos.2 (hηf I)) h1
    rwa [inv_inv] at h2
  refine ⟨∑ J : Finset (Fin n), |Rf J|, (∑ J : Finset (Fin n), (ηf J)⁻¹)⁻¹,
    inv_pos.2 hsum_pos, fun π hπ hπO => ?_⟩
  haveI := hπ.1
  have hzero : ∀ I, ¬ I ⊆ supp μ → π (F I) = 0 := by
    intro I hI
    by_contra hne
    have hrel : ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
        ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x A ∂π = π (A ∩ F I) :=
      fun t A hA => (restrict_rel hface hπ.2.1 hπ.2.2 I t A hA).1
    have hg := inv_restrict hπ.2.1 (measurableSet_F I) rfl hne (measure_ne_top _ _) hrel
    have hgF : ((π (F I))⁻¹ • π.restrict (F I)) (F I)ᶜ = 0 := by
      simp only [Measure.smul_apply, Measure.restrict_apply (measurableSet_F I).compl,
        Set.compl_inter_self, measure_empty, smul_eq_mul, mul_zero]
    have hpos := hRη I hI _ hg hgF
    have hle : ((π (F I))⁻¹ • π.restrict (F I)) (farSet μ (Rf I) (ηf I))
        ≤ (π (F I))⁻¹ * π (farSet μ (∑ J : Finset (Fin n), |Rf J|)
            (∑ J : Finset (Fin n), (ηf J)⁻¹)⁻¹) := by
      rw [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl ((Measure.restrict_apply_le _ _).trans
        (measure_mono (farSet_mono μ (hRle I) (hηle I))))
    rw [hπO, mul_zero] at hle
    exact absurd (le_antisymm hle zero_le) hpos.ne'
  have hsupp : ¬ (Finset.univ : Finset (Fin n)) ⊆ supp μ := by
    intro hu
    haveI := hμ.1.1.1
    have hc := concentrates hface hμ.1
    have hsub : faceInt μ ⊆ openOrthant n := fun x hx i => hx.2 i (hu (Finset.mem_univ i))
    have hu0 : μ Set.univ = 0 := by
      rw [← Set.union_compl_self (faceInt μ)]
      exact measure_union_null (measure_mono_null hsub hμ.2) hc
    simp at hu0
  have hπo : π (openOrthant n) = 0 :=
    measure_mono_null (show openOrthant n ⊆ F (Finset.univ : Finset (Fin n)) from
      fun x hx => ⟨fun i => (hx i).le, fun i =>
        ⟨fun _ => hx i, fun _ => Finset.mem_univ i⟩⟩) (hzero _ hsupp)
  obtain ⟨s, p, hs, hp, hp1, hπeq⟩ := conv_of_inv htot hface (fun I _ => hov I) hπ hπo
  refine ⟨s, p, ?_, hp, hp1, hπeq⟩
  intro ν hνs
  have hνE : ν ∈ bdryErgodic P X := hs hνs
  haveI := hνE.1.1.1
  have hνle : ∀ A : Set (SDEState n), (p ν : ℝ≥0∞) * ν A ≤ π A := by
    intro A
    rw [hπeq, Measure.coe_finset_sum, Finset.sum_apply]
    have h1 := Finset.single_le_sum (f := fun μ' => ((p μ' : ℝ≥0∞) • μ') A)
      (fun _ _ => zero_le) hνs
    simpa only [Measure.smul_apply, smul_eq_mul] using h1
  have hνzero : ∀ I, ¬ I ⊆ supp μ → ν (F I) = 0 := fun I hI => by
    have h1 := hνle (F I)
    rw [hzero I hI] at h1
    have h2 : (p ν : ℝ≥0∞) * ν (F I) = 0 := le_antisymm h1 zero_le
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (by exact_mod_cast (hp ν hνs).ne')
    · exact h
  have hνc := concentrates hface hνE.1
  have hνF : ν (F (supp ν))ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.2 (faceInt_subset_F ν)) hνc
  have hsub : supp ν ⊆ supp μ := by
    by_contra h
    have h0 := hνzero _ h
    have hu : ν Set.univ = 0 := by
      rw [← Set.union_compl_self (F (supp ν))]
      exact measure_union_null h0 hνF
    simp at hu
  by_cases heq : supp ν = supp μ
  · exact Or.inr (Set.mem_singleton_iff.2
      (eq_of_supp_eq hface htot (fun S _ => hov S) hνE.1 hνE.2 hμ.1 heq))
  · refine Or.inl ⟨hνE, measure_mono_null (Set.compl_subset_compl.2 ?_) hνc⟩
    intro x hx
    obtain ⟨j, hjμ, hjν⟩ : ∃ j ∈ supp μ, j ∉ supp ν := by
      by_contra hc
      push_neg at hc
      exact heq (Finset.Subset.antisymm hsub hc)
    refine ⟨⟨hx.1.1, fun i hi => hx.1.2 i (fun h => hi (hsub h))⟩, fun hint => ?_⟩
    have h3 := hint.2 j hjμ
    rw [hx.1.2 j hjν] at h3
    exact lt_irrefl _ h3

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

theorem isOpen_farSet (μ : Measure (SDEState n)) (R η : ℝ) : IsOpen (farSet μ R η) := by
  have e : farSet μ R η = {y : SDEState n | l1 y < R} ∩
      ⋃ i, ⋃ (_ : i ∉ supp μ), {y : SDEState n | η < y i} := by
    ext y; simp [farSet]
  rw [e]
  have hc : ∀ i : Fin n, Continuous fun y : SDEState n => y i := fun i =>
    PiLp.continuous_apply 2 _ i
  have hl : Continuous fun y : SDEState n => l1 y := by
    unfold l1
    exact continuous_finset_sum _ fun i _ => (hc i).abs
  exact (isOpen_lt hl continuous_const).inter
    (isOpen_iUnion fun i => isOpen_iUnion fun _ => isOpen_lt continuous_const (hc i))

theorem farSet_compl_nonempty (μ : Measure (SDEState n)) (R : ℝ) {η : ℝ} (hη : 0 < η) :
    (farSet μ R η)ᶜ.Nonempty := by
  refine ⟨0, fun h => ?_⟩
  obtain ⟨_, i, _, hi⟩ := h
  have h0 : (0 : SDEState n) i = 0 := rfl
  rw [h0] at hi
  linarith

/-- Portmanteau: a limit point of the occupation measures of a path that never visits the open
set `O` gives `O` no mass. -/
theorem limit_null_of_avoid {O : Set (SDEState n)} (hO : IsOpen O) (hOc : (Oᶜ).Nonempty)
    {x : SDEState n} {ω : Ω} (hav : ∀ t : ℝ≥0, X x t ω ∉ O) {π : Measure (SDEState n)}
    (hπ : π ∈ limitSet X x ω) : π O = 0 := by
  obtain ⟨hprob, ts, -, -, hlim⟩ := hπ
  haveI := hprob
  let f : C(SDEState n, ℝ) := ⟨fun y => min 1 (Metric.infDist y Oᶜ),
    continuous_const.min (Metric.continuous_infDist_pt _)⟩
  have hf01 : ∀ y, 0 ≤ f y ∧ f y ≤ 1 := fun y =>
    ⟨le_min zero_le_one Metric.infDist_nonneg, min_le_left _ _⟩
  let h : SDEState n →ᵇ ℝ := BoundedContinuousFunction.mkOfBound f 1 (fun y z => by
    rw [Real.dist_eq, abs_le]
    have h1 := hf01 y
    have h2 := hf01 z
    constructor <;> linarith)
  have hval : ∀ y, h y = min 1 (Metric.infDist y Oᶜ) := fun y => rfl
  have hzero : ∀ k, ∫ y, h y ∂(occ X x (ts k) ω) = 0 := by
    intro k
    unfold occ
    rw [integral_smul_measure]
    have hm : ∫ y, h y ∂((volume.restrict (Set.Icc (0 : ℝ) (ts k))).map
        (fun s : ℝ => X x s.toNNReal ω)) = 0 := by
      by_cases hf : AEMeasurable (fun s : ℝ => X x s.toNNReal ω)
          (volume.restrict (Set.Icc (0 : ℝ) (ts k)))
      · rw [integral_map hf h.continuous.aestronglyMeasurable]
        have h0 : ∀ s : ℝ, h (X x s.toNNReal ω) = 0 := fun s => by
          rw [hval, Metric.infDist_zero_of_mem (hav _), min_eq_right zero_le_one]
        simp only [h0, integral_zero]
      · rw [Measure.map_of_not_aemeasurable hf, integral_zero_measure]
    rw [hm, smul_zero]
  have hπ0 : ∫ y, h y ∂π = 0 :=
    tendsto_nhds_unique (hlim h) (by simp only [hzero]; exact tendsto_const_nhds)
  have hnn : 0 ≤ᵐ[π] fun y => h y := Eventually.of_forall fun y => (hf01 y).1
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (h.integrable π)).1 hπ0
  refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)
  have hpos : 0 < Metric.infDist y Oᶜ :=
    (hO.isClosed_compl.notMem_iff_infDist_pos hOc).1 (by simpa using hy)
  have hm : 0 < min 1 (Metric.infDist y Oᶜ) := lt_min one_pos hpos
  intro he
  have he' : h y = 0 := he
  rw [hval] at he'
  linarith

/-- The glue: lemma_5_9 from lemma_5_7, lemma_5_8, T1, T3 and the face structure. -/
theorem glue {C : Coeffs n} [IsFiniteMeasure P] (htot : TotOne P X) (hface : FaceInv P X)
    (hov : ∀ I : Finset (Fin n), FaceOverlap P X I)
    (h57 : ∀ x ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {μ | ∃ t : ℝ, 1 ≤ t ∧ μ = occ X x t ω} ∧
        ∀ π ∈ limitSet X x ω, IsInvariant P X π)
    (h58 : ∀ μ ∈ M1 P C X, ∀ x ∈ openOrthant n,
      P {ω | limitSet X x ω ⊆ conv (subErgodic P X μ ∪ {μ})}
        = P {ω | limitSet X x ω = {μ}})
    (hT1 : ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ R η : ℝ, 0 < η →
      ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ Kbox μ k Δ, 1 - ε < (P {ω | ∀ t : ℝ≥0,
        ¬ (l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i)}).toReal)
    (hT3 : ∀ μ : Measure (SDEState n), IsInvariant P X μ → ∀ x ∈ openOrthant n,
      ∀ᵐ ω ∂P, limitSet X x ω = {μ} → ∀ i,
        Tendsto (fun t : ℝ≥0 => Real.log (X x t ω i) / t) atTop (𝓝 (lyap C i μ))) :
    ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ x ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X x μ)).toReal := by
  intro μ hμ k hk ε hε
  obtain ⟨R, η, hη, hT2⟩ := exists_far htot hface hov hμ.1
  obtain ⟨Δ, hΔ, hbox⟩ := hT1 μ hμ k hk ε hε R η hη
  refine ⟨Δ, hΔ, fun x hx => (hbox x hx).trans_le (ENNReal.toReal_mono (measure_ne_top _ _) ?_)⟩
  have hxo : x ∈ openOrthant n := hx.1
  have hxr : x ∈ orthant n := fun i => (hxo i).le
  have hO := isOpen_farSet μ R η
  have hOc := farSet_compl_nonempty μ R hη
  calc P {ω | ∀ t : ℝ≥0, ¬ (l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i)}
      ≤ P {ω | limitSet X x ω ⊆ conv (subErgodic P X μ ∪ {μ})} := by
        refine measure_mono_ae ?_
        filter_upwards [h57 x hxr] with ω hω hN
        intro π hπ
        exact hT2 π (hω.2 π hπ) (limit_null_of_avoid hO hOc (fun t => hN t) hπ)
    _ = P {ω | limitSet X x ω = {μ}} := h58 μ hμ x hxo
    _ ≤ P (extinctEvent C X x μ) := by
        refine measure_mono_ae ?_
        filter_upwards [hT3 μ hμ.1.1.1 x hxo] with ω hω hU
        exact ⟨hU, fun i hi => ⟨hω hU i, hμ.2.1 i hi⟩⟩

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

/-- The Lyapunov integrand `hᵢ = fᵢ − σᵢᵢgᵢ²/2` is dominated by the growth weight with `δ = 0`. -/
theorem lyapF_bound (C : Coeffs n) (c : SDEState n) (i : Fin n) (y : SDEState n) :
    |C.f i y - C.sig i i * C.g i y ^ 2 / 2| < (1 + |C.sig i i|) * growthWeight C c 0 y := by
  unfold growthWeight
  rw [Real.rpow_zero, one_mul]
  have hs : |C.f i y| + C.g i y ^ 2 ≤ ∑ j, (|C.f j y| + C.g j y ^ 2) :=
    Finset.single_le_sum (f := fun j => |C.f j y| + C.g j y ^ 2)
      (fun j _ => add_nonneg (abs_nonneg _) (sq_nonneg _)) (Finset.mem_univ i)
  have hg : 0 ≤ C.g i y ^ 2 := sq_nonneg _
  have hσ : 0 ≤ |C.sig i i| := abs_nonneg _
  have hf : 0 ≤ |C.f i y| := abs_nonneg _
  have habs : |C.f i y - C.sig i i * C.g i y ^ 2 / 2| ≤ |C.f i y| + |C.sig i i| * C.g i y ^ 2 := by
    calc |C.f i y - C.sig i i * C.g i y ^ 2 / 2|
        ≤ |C.f i y| + |C.sig i i * C.g i y ^ 2 / 2| := abs_sub _ _
      _ = |C.f i y| + |C.sig i i| * C.g i y ^ 2 / 2 := by
          rw [abs_div, abs_mul, abs_of_nonneg hg, abs_two]
      _ ≤ |C.f i y| + |C.sig i i| * C.g i y ^ 2 := by
          have : 0 ≤ |C.sig i i| * C.g i y ^ 2 := mul_nonneg hσ hg
          linarith
  have hS0 : 0 ≤ ∑ j, (|C.f j y| + C.g j y ^ 2) := le_trans (add_nonneg hf hg) hs
  have key : |C.f i y| + |C.sig i i| * C.g i y ^ 2
      ≤ (1 + |C.sig i i|) * (∑ j, (|C.f j y| + C.g j y ^ 2)) := by
    have e1 : |C.sig i i| * C.g i y ^ 2 ≤ |C.sig i i| * ∑ j, (|C.f j y| + C.g j y ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hσ
    have e2 : |C.f i y| ≤ ∑ j, (|C.f j y| + C.g j y ^ 2) := by linarith
    nlinarith
  have hlt : (1 + |C.sig i i|) * (∑ j, (|C.f j y| + C.g j y ^ 2))
      < (1 + |C.sig i i|) * (1 + ∑ j, (|C.f j y| + C.g j y ^ 2)) := by
    have : 0 < 1 + |C.sig i i| := by linarith
    nlinarith
  linarith

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

theorem isProb_occ (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) {T : ℝ} (hT : 0 < T) :
    IsProbabilityMeasure (occ X x T ω) := by
  have hm : Measurable fun s : ℝ => X x s.toNNReal ω :=
    (hc.comp continuous_real_toNNReal).measurable
  constructor
  unfold occ
  rw [Measure.smul_apply, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, smul_eq_mul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hT).ne' ENNReal.ofReal_ne_top]

theorem avg_of_limitSet (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (μ : Measure (SDEState n))
    (hL : limitSet X x ω = {μ})
    (hT : IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X x t ω}) (h : SDEState n →ᵇ ℝ) :
    Tendsto (fun T : ℝ => ∫ y, h y ∂(occ X x T ω)) atTop (𝓝 (∫ y, h y ∂μ)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  let S : Set (ProbabilityMeasure (SDEState n)) :=
    {ν | ∃ t : ℝ, 1 ≤ t ∧ (ν : Measure (SDEState n)) = occ X x t ω}
  have hS : IsTightMeasureSet {((ν : ProbabilityMeasure (SDEState n)) : Measure (SDEState n)) |
      ν ∈ S} := by
    refine hT.subset ?_
    rintro _ ⟨ν, ⟨t, ht, he⟩, rfl⟩
    exact ⟨t, ht, he⟩
  have hK := isCompact_closure_of_isTightMeasureSet hS
  let νs : ℕ → ProbabilityMeasure (SDEState n) := fun k =>
    ⟨occ X x (max (ns k) 1) ω, isProb_occ X x ω hc (lt_of_lt_of_le one_pos (le_max_right _ _))⟩
  have hmem : ∀ k, νs k ∈ closure S := fun k =>
    subset_closure ⟨max (ns k) 1, le_max_right _ _, rfl⟩
  obtain ⟨π, -, φ, hφ, hπ⟩ := hK.tendsto_subseq hmem
  have hns' : Tendsto (fun k => ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hts : Tendsto (fun k => max (ns (φ k)) 1) atTop atTop :=
    tendsto_atTop_mono (fun k => le_max_left _ _) hns'
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hπ
  have hπL : (π : Measure (SDEState n)) ∈ limitSet X x ω :=
    ⟨inferInstance, fun k => max (ns (φ k)) 1, fun k => le_max_right _ _, hts, fun g => hint g⟩
  rw [hL, Set.mem_singleton_iff] at hπL
  refine ⟨φ, ?_⟩
  have h2 := hint h
  rw [hπL] at h2
  refine h2.congr' ?_
  filter_upwards [hns'.eventually_ge_atTop 1] with k hk
  show ∫ y, h y ∂(occ X x (max (ns (φ k)) 1) ω) = ∫ y, h y ∂(occ X x (ns (φ k)) ω)
  rw [max_eq_left hk]

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

theorem sq_le_growthWeight (C : Coeffs n) {c : SDEState n} (hc : c ∈ openOrthant n) {δ : ℝ}
    (hδ : 0 ≤ δ) {y : SDEState n} (hy : y ∈ orthant n) (i : Fin n) :
    C.g i y ^ 2 ≤ growthWeight C c δ y := by
  unfold growthWeight
  have h1 : 1 ≤ (1 + ∑ j, c j * y j) ^ δ := Real.one_le_rpow
    (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => mul_nonneg (hc j).le (hy j))) hδ
  have h2 : C.g i y ^ 2 ≤ 1 + ∑ j, (|C.f j y| + C.g j y ^ 2) := by
    have := Finset.single_le_sum (f := fun j => |C.f j y| + C.g j y ^ 2)
      (fun j _ => add_nonneg (abs_nonneg _) (sq_nonneg _)) (Finset.mem_univ i)
    linarith [abs_nonneg (C.f i y)]
  have h3 : 0 ≤ 1 + ∑ j, (|C.f j y| + C.g j y ^ 2) := le_trans (sq_nonneg _) h2
  calc C.g i y ^ 2 ≤ 1 + ∑ j, (|C.f j y| + C.g j y ^ 2) := h2
    _ = 1 * (1 + ∑ j, (|C.f j y| + C.g j y ^ 2)) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 h3

/-- The quadratic-variation bound of the child from lemma 5.4 clause 1. -/
theorem hQ_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (c : SDEState n) (hc : c ∈ openOrthant n)
    (hgc : ∀ i, ContinuousOn (C.g i) (orthant n)) (x : SDEState n)
    (hcont : ∀ ω, Continuous fun s => X x s ω) (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h54 : ∃ Khat : ℝ, 0 < Khat ∧ ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t)) :
    ∃ K : ℝ, ∀ᵐ ω ∂P, ∀ i, ∀ᶠ t : ℝ in atTop,
      ∫ u in (0 : ℝ)..t, C.g i (X x u.toNNReal ω) ^ 2 ≤ K * t := by
  obtain ⟨Kh, hKh, hK⟩ := h54
  refine ⟨Kh + 1, ?_⟩
  filter_upwards [hK, hstay] with ω hω hs i
  filter_upwards [hω 1 one_pos, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  have hpc : Continuous fun u : ℝ => X x u.toNNReal ω :=
    (hcont ω).comp continuous_real_toNNReal
  have hgc' : Continuous fun u : ℝ => C.g i (X x u.toNNReal ω) ^ 2 :=
    ((hgc i).comp_continuous hpc (fun u => hs _)).pow 2
  have hint : IntegrableOn (fun u : ℝ => C.g i (X x u.toNNReal ω) ^ 2) (Set.Icc 0 t) :=
    hgc'.continuousOn.integrableOn_compact isCompact_Icc
  have heq : ∫ u in (0 : ℝ)..t, C.g i (X x u.toNNReal ω) ^ 2
      = ∫ u in Set.Icc (0 : ℝ) t, C.g i (X x u.toNNReal ω) ^ 2 := by
    rw [intervalIntegral.integral_of_le ht0, integral_Icc_eq_integral_Ioc]
  rw [heq]
  have hle : ENNReal.ofReal (∫ u in Set.Icc (0 : ℝ) t, C.g i (X x u.toNNReal ω) ^ 2)
      ≤ ENNReal.ofReal ((Kh + 1) * t) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun u => sq_nonneg _)]
    refine le_trans (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_) ht
    exact sq_le_growthWeight C hc hδ (hs _) i
  have hR : 0 ≤ (Kh + 1) * t := mul_nonneg (by linarith) ht0
  exact (ENNReal.ofReal_le_ofReal_iff hR).1 hle

theorem measurableSet_orthant' : MeasurableSet (orthant n) := by
  have e : orthant n = ⋂ i, {x : SDEState n | 0 ≤ x i} := by
    ext x; simp [orthant]
  rw [e]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le measurable_const (PiLp.continuous_apply 2 _ i).measurable

/-- `occ_integral` for an unbounded `h` continuous on the orthant (path in the orthant). -/
theorem occ_integral_cont (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (hs : ∀ s, X x s ω ∈ orthant n) {T : ℝ} (hT : 0 < T)
    {h : SDEState n → ℝ} (hh : ContinuousOn h (orthant n)) :
    ∫ y, h y ∂(occ X x T ω) = T⁻¹ * ∫ s in (0 : ℝ)..T, h (X x s.toNNReal ω) := by
  have hm : Measurable fun s : ℝ => X x s.toNNReal ω :=
    (hc.comp continuous_real_toNNReal).measurable
  have hae : ∀ᵐ y ∂((volume.restrict (Set.Icc (0 : ℝ) T)).map (fun s => X x s.toNNReal ω)),
      y ∈ orthant n :=
    (ae_map_iff hm.aemeasurable measurableSet_orthant').2 (ae_of_all _ fun s => hs _)
  have hsm : AEStronglyMeasurable h
      ((volume.restrict (Set.Icc (0 : ℝ) T)).map (fun s => X x s.toNNReal ω)) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hh.aestronglyMeasurable measurableSet_orthant'
  unfold occ
  rw [integral_smul_measure, integral_map hm.aemeasurable hsm,
    intervalIntegral.integral_of_le hT.le, integral_Icc_eq_integral_Ioc, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hT.le, smul_eq_mul]

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

/-- Conclusion of the NEW child `log_lln_continuous` at one starting point. -/
def LogLLNCont [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) : Prop :=
  (∃ K : ℝ, ∀ᵐ ω ∂P, ∀ i, ∀ᶠ t : ℝ in atTop,
      ∫ u in (0 : ℝ)..t, C.g i (X x u.toNNReal ω) ^ 2 ≤ K * t) →
    ∀ᵐ ω ∂P, ∀ i, Tendsto (fun t : ℝ≥0 =>
      Real.log (X x t ω i) / (t : ℝ)
      - (t : ℝ)⁻¹ * ∫ u in (0 : ℝ)..(t : ℝ),
          (C.f i (X x u.toNNReal ω) - C.sig i i * C.g i (X x u.toNNReal ω) ^ 2 / 2))
        atTop (𝓝 0)

/-- Real-time averages of `hᵢ` converge to `λᵢ(μ)` on `{U = {μ}}` (5.6 along every sequence). -/
theorem avg_tendsto [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (c : SDEState n) (δ₁ : ℝ) (hδ₁ : 0 < δ₁)
    (hfc : ∀ i, ContinuousOn (C.f i) (orthant n)) (hgc : ∀ i, ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (ω : Ω) (hc : Continuous fun s => X x s ω)
    (hs : ∀ t, X x t ω ∈ orthant n)
    (h56 : ∀ Khat : ℝ,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t)) →
      ∀ (Ts : ℕ → ℝ) (π : Measure (SDEState n)), Tendsto Ts atTop atTop → IsInvariant P X π →
      (∀ h : SDEState n →ᵇ ℝ,
        Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π))) →
      ∀ (h : SDEState n → ℝ) (Kh δ : ℝ), ContinuousOn h (orthant n) → 0 < Kh → 0 ≤ δ →
        δ < δ₁ → (∀ y ∈ orthant n, |h y| < Kh * growthWeight C c δ y) →
        Integrable h π ∧
          Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π)))
    (Khat : ℝ) (hK : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t))
    (μ : Measure (SDEState n)) (hμ : IsInvariant P X μ)
    (hconv : ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun T : ℝ => ∫ y, h y ∂(occ X x T ω)) atTop (𝓝 (∫ y, h y ∂μ))) (i : Fin n) :
    Tendsto (fun T : ℝ => ∫ y, (C.f i y - C.sig i i * C.g i y ^ 2 / 2) ∂(occ X x T ω))
      atTop (𝓝 (lyap C i μ)) := by
  have hcon : ContinuousOn (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) (orthant n) :=
    (hfc i).sub ((continuousOn_const.mul ((hgc i).pow 2)).div_const 2)
  have hKh : (0 : ℝ) < 1 + |C.sig i i| := by have := abs_nonneg (C.sig i i); linarith
  refine tendsto_of_seq_tendsto fun Ts hTs => ?_
  exact (h56 Khat hK Ts μ hTs hμ (fun h => (hconv h).comp hTs) _ (1 + |C.sig i i|) 0 hcon hKh
    le_rfl hδ₁ (fun y _ => UcGlue.lyapF_bound C c i y)).2

/-- T3 at one starting point from `LogLLNCont` + 5.4 cl. 1 + 5.6 + 5.7. -/
theorem T3_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (c : SDEState n) (hc : c ∈ openOrthant n)
    (δ₁ : ℝ) (hδ₁ : 0 < δ₁)
    (hfc : ∀ i, ContinuousOn (C.f i) (orthant n)) (hgc : ∀ i, ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (hcont : ∀ ω, Continuous fun s => X x s ω)
    (h56 : ∀ ω : Ω, (∀ t, X x t ω ∈ orthant n) → ∀ Khat : ℝ,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t)) →
      ∀ (Ts : ℕ → ℝ) (π : Measure (SDEState n)), Tendsto Ts atTop atTop → IsInvariant P X π →
      (∀ h : SDEState n →ᵇ ℝ,
        Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π))) →
      ∀ (h : SDEState n → ℝ) (Kh δ : ℝ), ContinuousOn h (orthant n) → 0 < Kh → 0 ≤ δ →
        δ < δ₁ → (∀ y ∈ orthant n, |h y| < Kh * growthWeight C c δ y) →
        Integrable h π ∧
          Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π)))
    (h54 : ∃ Khat : ℝ, 0 < Khat ∧ ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t))
    (h57 : ∀ᵐ ω ∂P, IsTightMeasureSet {μ | ∃ t : ℝ, 1 ≤ t ∧ μ = occ X x t ω})
    (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n)
    (hchild : LogLLNCont P C X x)
    (μ : Measure (SDEState n)) (hμ : IsInvariant P X μ) :
    ∀ᵐ ω ∂P, limitSet X x ω = {μ} → ∀ i,
      Tendsto (fun t : ℝ≥0 => Real.log (X x t ω i) / t) atTop (𝓝 (lyap C i μ)) := by
  have hQ := HLglue.hQ_of P C X c hc hgc x hcont hstay hδ₁.le h54
  obtain ⟨Kh, -, hKh⟩ := h54
  filter_upwards [hchild hQ, h57, hstay, hKh] with ω h1 hT hs hK hU i
  have hconv := fun h => LimOcc.avg_of_limitSet X x ω (hcont ω) μ hU hT h
  have hA := avg_tendsto P C X c δ₁ hδ₁ hfc hgc x ω (hcont ω) hs (h56 ω hs) Kh hK μ hμ hconv i
  have hA' := hA.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hcon : ContinuousOn (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) (orthant n) :=
    (hfc i).sub ((continuousOn_const.mul ((hgc i).pow 2)).div_const 2)
  have hsum := (h1 i).add hA'
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
  have ht' : (0 : ℝ) < t := ht
  have e := HLglue.occ_integral_cont X x ω (hcont ω) hs ht' hcon
  simp only [Function.comp_apply, id]
  rw [e]
  ring

end StochKolmogorov.Classify.L59T3

end FlatM_T3glue

-- ===== Face (copied from the 8f909832 top reduction) =====
-- ===== module Face =====
section Mod_Face

/-! FaceOverlap (the open analytic child of K1) from the PROVED platform theorem
`StochKolmogorov.Persist.kolmogorov_face_box_tv_overlap` (44879068), whose model definitions are
literally those of `Classify` (same file modulo the namespace). Here its conclusion is a hypothesis
`hTV`; the reduction supplies it from the child theorem applied to `persistCoeffs C`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.Face

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing StochKolmogorov.Classify.K1

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

/-- The same coefficients, read as `Persist` coefficients. -/
def persistCoeffs (C : Coeffs n) : StochKolmogorov.Persist.Coeffs n := ⟨C.f, C.g, C.Γ⟩

theorem persist_family {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hX : IsSolutionFamily P C B X) :
    StochKolmogorov.Persist.IsSolutionFamily P (persistCoeffs C) B X := hX

theorem persist_hC {C : Coeffs n}
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ∀ i, LocallyLipschitzOn (StochKolmogorov.Persist.orthant n) ((persistCoeffs C).f i) ∧
      LocallyLipschitzOn (StochKolmogorov.Persist.orthant n) ((persistCoeffs C).g i) := hC

theorem persist_hpd {C : Coeffs n}
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef) :
    ∀ x ∈ StochKolmogorov.Persist.orthant n, (Matrix.of fun i j => (persistCoeffs C).g i x *
      (persistCoeffs C).g j x * (persistCoeffs C).sig i j).PosDef := hpd

/-- The conclusion of `kolmogorov_face_box_tv_overlap` for the family `X`. -/
def FaceTV (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  ∀ (I : Finset (Fin n)) {α β : ℝ}, 0 < α → α ≤ β →
    ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ StochKolmogorov.Persist.faceOpen I, (∀ i ∈ I, α ≤ x i ∧ x i ≤ β) →
      ∀ y ∈ StochKolmogorov.Persist.faceOpen I, (∀ i ∈ I, α ≤ y i ∧ y i ≤ β) →
        MarkovChainCLT.tvDist (StochKolmogorov.Persist.trans P X T x)
          (StochKolmogorov.Persist.trans P X T y) ≤ 1 - ε

theorem faceBox_faceOpen {S : Finset (Fin n)} {a b : ℝ} {x : SDEState n}
    (hx : x ∈ faceBox S a b) : x ∈ StochKolmogorov.Persist.faceOpen S := by
  refine ⟨hx.1.1, fun i hi => ?_, fun i hi => (hx.1.2 i).1 hi⟩
  have h1 : 0 ≤ x i := hx.1.1 i
  have h2 : ¬ 0 < x i := fun h => hi ((hx.1.2 i).2 h)
  exact le_antisymm (not_lt.1 h2) h1

theorem abs_le_tvDist (μ ν : Measure (SDEState n)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {A : Set (SDEState n)} (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ MarkovChainCLT.tvDist μ ν := by
  unfold MarkovChainCLT.tvDist
  refine le_csSup ⟨1, ?_⟩ ⟨A, hA, rfl⟩
  rintro r ⟨B, -, rfl⟩
  have h1 : (μ B).toReal ≤ 1 := by
    have := prob_le_one (μ := μ) (s := B)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have h2 : (ν B).toReal ≤ 1 := by
    have := prob_le_one (μ := ν) (s := B)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  rw [abs_le]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := μ B), ENNReal.toReal_nonneg (a := ν B)]

theorem eps_le_of_tvDist (μ ν : Measure (SDEState n)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {ε : ℝ} (h : MarkovChainCLT.tvDist μ ν ≤ 1 - ε)
    {A : Set (SDEState n)} (hA : MeasurableSet A) :
    ENNReal.ofReal ε ≤ μ A + ν Aᶜ := by
  have h0 := (abs_le_tvDist μ ν hA).trans h
  have hc : (ν Aᶜ).toReal = 1 - (ν A).toReal := by
    rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have e : μ A + ν Aᶜ = ENNReal.ofReal ((μ A).toReal + (ν Aᶜ).toReal) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top μ A), ENNReal.ofReal_toReal (measure_ne_top ν Aᶜ)]
  rw [e]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hc]
  have := (abs_le.1 h0).1
  linarith

theorem faceOverlap_of_tv {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hX : IsSolutionFamily P C B X) (hTV : FaceTV P X) (S : Finset (Fin n)) :
    FaceOverlap P X S := by
  haveI : IsProbabilityMeasure P := hX.1
  intro a b ha hab
  obtain ⟨T, ε, hε, hT⟩ := hTV S ha hab
  refine ⟨T, ENNReal.ofReal ε, ENNReal.ofReal_pos.2 hε, fun x hx y hy A hA => ?_⟩
  have hxo := faceBox_faceOpen hx
  have hyo := faceBox_faceOpen hy
  have hmx : Measurable (X x T) := (hX.2.2 x hx.1.1).1 T
  have hmy : Measurable (X y T) := (hX.2.2 y hy.1.1).1 T
  haveI : IsProbabilityMeasure (StochKolmogorov.Persist.trans P X T x) :=
    Measure.isProbabilityMeasure_map hmx.aemeasurable
  haveI : IsProbabilityMeasure (StochKolmogorov.Persist.trans P X T y) :=
    Measure.isProbabilityMeasure_map hmy.aemeasurable
  exact eps_le_of_tvDist _ _ (hT x hxo (fun i hi => hx.2 i hi) y hyo (fun i hi => hy.2 i hi)) hA

end StochKolmogorov.Classify.Face

end Mod_Face

-- ===== top glue of lemma_5_9 =====
section L59TopSec

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.L59Top

open StochKolmogorov.Classify EthierKurtz

/-- Assumption 1.4 is monotone in `δ₁` (only large `‖x‖ ≥ 1` matters). -/
theorem a14_mono {n : ℕ} (C : Coeffs n) {δ₁ δ' : ℝ} (h14 : Assumption14 C δ₁)
    (hδ' : 0 < δ') (hle : δ' ≤ δ₁) : Assumption14 C δ' := by
  refine ⟨hδ', ?_⟩
  have hev : ∀ᶠ x in comap l1 atTop ⊓ 𝓟 (orthant n), 1 ≤ l1 x :=
    Filter.Eventually.filter_mono inf_le_left
      (Filter.tendsto_comap.eventually (eventually_ge_atTop 1))
  refine squeeze_zero' (Filter.Eventually.of_forall fun x => ?_) (hev.mono fun x hx => ?_) h14.2
  · have hl : 0 ≤ l1 x := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hD : 0 ≤ 1 + ∑ i, (|C.f i x| + C.g i x ^ 2) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun i _ =>
        add_nonneg (abs_nonneg _) (sq_nonneg _))
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hl _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)) hD
  · have hD : 0 ≤ 1 + ∑ i, (|C.f i x| + C.g i x ^ 2) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun i _ =>
        add_nonneg (abs_nonneg _) (sq_nonneg _))
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hx hle) (Finset.sum_nonneg fun i _ => sq_nonneg _)) hD

theorem stay_of {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hcl : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0))
    (x : SDEState n) (hx : x ∈ orthant n) : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n := by
  classical
  filter_upwards [hcl (Finset.univ.filter fun i => 0 < x i) x hx (fun i => by simp)] with ω hω t
  show ∀ i, 0 ≤ X x t ω i
  intro i
  by_cases hi : 0 < x i
  · exact ((hω t).1 i (by simp [hi])).le
  · rw [(hω t).2 i (by simp [hi])]

theorem stay_open_of {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hcl : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0))
    (x : SDEState n) (hx : x ∈ openOrthant n) : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ openOrthant n := by
  have hxo : x ∈ orthant n := fun i => (hx i).le
  filter_upwards [hcl Finset.univ x hxo (fun i => ⟨fun _ => hx i, fun _ => Finset.mem_univ i⟩)]
    with ω hω t
  exact fun i => (hω t).1 i (Finset.mem_univ i)

/-- Lemma 5.9 from lemmas 5.4, 5.6, 5.7, 5.8, Extinct 3.1, Persist face TV overlap and the two
new children `sink_box_avoids_far_set` (T1) and `log_lln_continuous` (T3). -/
theorem main {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ x ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X x μ)).toReal := by
  haveI : IsProbabilityMeasure P := hX.1
  have hpd := hA.1
  have hC := hA.2.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  obtain ⟨δ₀, hδ₀⟩ := GE.exists_isDelta0 C γb hγ
  have hcl : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0) :=
    (StochKolmogorov.Extinct.lemma_3_1 hn P ⟨C.f, C.g, C.Γ⟩ B X hX c γb hA _
      (GE.delta_small C hδ₀)).2.1
  have hfc : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hC i).1.continuousOn
  have hgc : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hC i).2.continuousOn
  have hδ' : 0 < min δ₁ δ₀ := lt_min h14.1 hδ₀.1
  have h14' := a14_mono C h14 hδ' (min_le_left _ _)
  obtain ⟨K54, hK54, h54⟩ :=
    (lemma_5_4 hn P C B X hX c γb hA δ₀ hδ₀ _ h14' (min_le_right _ _)).1
  have h57 := lemma_5_7 hn P C B X hX c γb hA δ₁ h14
  refine L59.glue (K1.totOne_of_family hX) (K1a.faceInv_of_clause hcl)
    (fun I => Face.faceOverlap_of_tv hX (fun I _ _ ha hab =>
      StochKolmogorov.Persist.kolmogorov_face_box_tv_overlap P (Face.persistCoeffs C) B X
        (Face.persist_family hX) (Face.persist_hC hC) (Face.persist_hpd hpd) I ha hab) I)
    h57 (lemma_5_8 hn P C B X hX c γb hA δ₁ h14)
    (sink_box_avoids_far_set P C B X hX c γb hA) ?_
  intro μ hμ x hx
  have hxo : x ∈ orthant n := fun i => (hx i).le
  exact L59T3.T3_of P C X c hc (min δ₁ δ₀) hδ' hfc hgc x (hX.2.2 x hxo).2.1
    (lemma_5_6 hn P C B X hX c γb hA δ₀ hδ₀ _ h14' (min_le_right _ _) x hxo)
    ⟨K54, hK54, h54 x hxo⟩ ((h57 x hxo).mono fun ω h => h.1) (stay_of P X hcl x hxo)
    (log_lln_continuous P C B X hX (fun i => ⟨hfc i, hgc i⟩) x hx (stay_open_of P X hcl x hx))
    μ hμ

end StochKolmogorov.Classify.L59Top

end L59TopSec

open MeasureTheory ProbabilityTheory Filter StochKolmogorov.Classify EthierKurtz in
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ x ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X x μ)).toReal := by
  exact StochKolmogorov.Classify.L59Top.main hn P C B X hX c γb hA δ₁ h14
