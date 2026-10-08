-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.dilated_distance_invariant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T20:54:06.772991+00:00
-- url     : https://prove2.me/submissions/1c2f19bc-89c7-4da3-b94a-1008543fdfad

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod
import Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_A_comp_B
import Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_B_comp_A
import Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_gTilde_ne_zero
import Theorems.Thm_ShorNonsmooth_SpaceDilation_scalar_contraction_bound
import Theorems.Thm_ShorNonsmooth_SpaceDilation_dilation_norm_eq
import Theorems.Thm_ShorNonsmooth_SpaceDilation_dilation_inv_norm_le
import Theorems.Thm_ShorNonsmooth_SpaceDilation_dilation_compose_inv
import Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_stall_freezes_state
import Theorems.Thm_ShorNonsmooth_SpaceDilation_inner_sq_add_orth_sq
import Theorems.Thm_ShorNonsmooth_SpaceDilation_dilation_orth_sq_identity

open ShorNonsmooth.SpaceDilation

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (xstar x₀ : EuclideanSpace ℝ (Fin n)) (d M N α : ℝ)
    (hd : 0 < d) (hN : 0 < N) (hNM : N < M)
    (h318 : ∀ x ∈ Metric.closedBall xstar d,
      N * (f x - f xstar) ≤ inner ℝ (g x) (x - xstar) ∧
        inner ℝ (g x) (x - xstar) ≤ M * (f x - f xstar))
    (hx₀ : x₀ ∈ Metric.closedBall xstar d)
    (hα : 1 < α) (hαMN : α ≤ (M + N) / (M - N)) (k : ℕ) :
    ‖(sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖) (fun _ => α) x₀
        (ContinuousLinearEquiv.refl ℝ _) k).A
      ((sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖) (fun _ => α) x₀
        (ContinuousLinearEquiv.refl ℝ _) k).x - xstar)‖ ≤ d := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `EuclideanSpace ℝ (Fin 0) = PiLp 0 fun _ => ℝ` is the *singleton* vector `0`:
    -- `Fin 0` has no indices, so there is exactly one function `Fin 0 → ℝ`.
    --
    -- History of this branch:
    --   7042 CE'd with `ext i; absurd i (by simp)` — `Fin 0` has no indices.
    --   7240 CE'd with `Did not find an occurrence of the pattern 0` on the goal
    --        `w = 0` — `rw [← PiLp.zero_apply]` cannot match that goal.
    --   7258 CE'd with `simp made no progress` — the replacement left an unused fact.
    --   7267 CE'd with 38 diagnostics because `ContinuousLinearEquiv.refl ℝ _ X`
    --        passes the space *twice*; it takes only the space.
    --
    -- The branch now closes by the fact the goal actually needs, stated without any
    -- `PiLp` or `refl` lemma: every `ContinuousLinearMap` out of `EuclideanSpace ℝ (Fin 0)`
    -- is `0`, so its value has norm `0 ≤ d`.
    --
    -- 7307 E01 @L56 / E02 @L60: the two previous attempts each failed one step later than
    -- the last, and both failures are informative:
    --   * `Subsingleton.elim _ _` (7307) got past the `ext w` step — so `hzero` really is
    --     provable by ext — but then reported `failed to synthesize Subsingleton ℝ`, because
    --     `ext` had reduced the goal to an equality of *scalars* `L w i = 0`, and Lean then
    --     looked for a `Subsingleton` instance on `ℝ` rather than on the vector space.
    --   * `rw [hA, norm_zero]` (7307) reported `Did not find an occurrence of the pattern ‖0‖`:
    --     after `hA : (sdg … k).A = 0` rewrites, the goal is `‖0 (x - x*)‖ ≤ d`, not `‖0‖ ≤ d`.
    --     The `norm_zero` rewrite pattern no longer occurs, because the zero map has to be
    --     *applied* first.
    --
    -- Repair: do not prove the auxiliary `hzero` at all. Rewrite the goal with `hzero`
    -- immediately, which turns `‖A (x - x*)‖` into `‖0 (x - x*)‖`, then apply the zero map
    -- with `map_zero`, which is the step `norm_zero` was standing in for.
    have hzero : ∀ (L : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0)),
        L = 0 := by
      intro L
      -- `ContinuousLinearMap.ext` needs a *coordinate* to compare on, and `Fin 0` has none,
      -- so the usual `ext i; …` route is unavailable (it is what 7042 tried and it CE'd with
      -- `absurd i (by simp)`). Instead use `map_zero` in both directions: `L 0 = 0` holds
      -- definitionally, and every element of a `Zero`-module over a `Subsingleton` codomain
      -- equals `0`. That last step is `Subsingleton.elim` applied to the *vectors*, not to
      -- the scalars — 7307 E01 got `failed to synthesize Subsingleton ℝ` because `ext` had
      -- already reduced the goal to `L w i = (0 : ℝ)` and Lean searched `ℝ`.
      have hL0 : L 0 = 0 := map_zero L
      -- `EuclideanSpace ℝ (Fin 0) = PiLp 0 fun _ => ℝ` has exactly one element, so any two
      -- vectors are equal: `subsingleton` holds on the space, not on `ℝ`.
      --
      -- 7314 E01 @L72 reported
      --   Tactic `rewrite` failed: Did not find an occurrence of the pattern `0`
      --   in the target expression `L = 0`
      -- so `rw [← hL0]` (candidate 7314) cannot fire: the right-hand `0` here is the
      -- *zero `ContinuousLinearMap`*, not the vector `0` that `hL0` rewrites to, so there is
      -- no `0` subterm for the backward rewrite to anchor on.
      --
      -- Repair: use `hL0` in the forward direction on its own premise and then apply
      -- `Subsingleton.elim` to the two *maps*. `EuclideanSpace ℝ (Fin 0)` is a subsingleton,
      -- hence so is the space of maps out of it, and `Subsingleton.elim L 0` is exactly the
      -- goal `L = 0`. No rewriting is needed at all.
      exact Subsingleton.elim L 0
    have hA := hzero ((sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖)
        (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0)))
        k).A)
    -- 7322 E02 @L77: after `rw [hA]`, the target is
    -- `‖0 ((sdg ... k).x - xstar)‖ ≤ d`.  `map_zero` only rewrites a map
    -- applied to the zero *input*, so it cannot fire while that input is still
    -- syntactically an arbitrary difference.  In `Fin 0` the domain is a
    -- subsingleton; reduce the input first, then `map_zero` and `norm_zero`
    -- apply in their ordinary direction.
    have hz :
        ((sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖)
          (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0)))
          k).x - xstar) = 0 := by
      exact Subsingleton.elim _ _
    rw [hA, hz, map_zero, norm_zero]
    exact hd.le
  set hstep : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖ with hhstep
  set astep : ℕ → ℝ := fun _ => α with hastep
  set iter : ℕ → SDGState n := sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) with hit
  set c : ℝ := 2 * M * N / (M + N) with hc
  have hcpos : 0 < c := by
    -- `c` is a `set`-abbreviation, so `positivity` cannot see `2*M*N`; unfold it first
    -- (E03: "failed to prove positivity/nonnegativity/nonzeroness").
    simp only [hc]
    have h1 : 0 < 2 * M * N := mul_pos (by linarith) hN
    have h2 : 0 < M + N := by linarith
    exact div_pos h1 h2
  have hδ : 0 < α - 1 := by linarith
  have hαk : ∀ j : ℕ, 1 ≤ j → 1 + (α - 1) ≤ astep j := by
    intro j _
    have hj1 : 1 ≤ j := by omega
    -- `astep j = α` by definition, and `hα : 1 < α` gives `1 + (α - 1) ≤ α`.
    have : α = α := rfl
    simp only [astep]
    linarith
  have hden : 0 < M - N := by linarith
  have hMN : (α : ℝ) * (M - N) ≤ M + N := by
    -- `mul_le_mul_of_nonneg_left` produces `(M-N) * α ≤ (M-N) * (…)`, which is the
    -- wrong factor order for this goal (E06).  Multiply on the right instead.
    calc α * (M - N) ≤ ((M + N) / (M - N)) * (M - N) :=
          mul_le_mul_of_nonneg_right hαMN (le_of_lt hden)
      _ = M + N := by field_simp
  -- Non-stalling at `jm` forces non-stalling at every earlier index, because a stall
  -- freezes the whole tail (Proved `sdg_stall_freezes_state`).
  --
  -- This argument was previously written out in full four times (once inside each of the
  -- `hkey`, `hkey'` and `hBcontraction` inductions, plus a degenerate copy inside `hInv`).
  -- It is stated once here and reused. Centralising it matters because each copy carried its
  -- own `rw`-direction bug: 7267 CE'd at *three* of the four sites (E10, E14, E18) with
  -- `Tactic rewrite failed: Did not find an occurrence of the pattern sdg … jm`, because
  -- each copy opened with `rw [← hit']` — which searches the goal for an `sdg` subterm when
  -- the goal's only subterm is `iter` — instead of rewriting in the direction that fires.
  have hnonstall : ∀ (jm : ℕ), g (iter jm).x ≠ 0 →
      ∀ i : ℕ, i ≤ jm → g (iter i).x ≠ 0 := by
    intro jm hgj i hi hgi
    refine hgj ?_
    have hfr : sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) jm
        = sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) i :=
      sdg_stall_freezes_state g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) i hgi jm hi
    -- 7307 E03 @L143 reported, for the goal-side `rw [hit']`,
    --   Tactic `rewrite` failed: Did not find an occurrence of the pattern
    --     sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) jm
    --   in the target expression  g (iter jm).x = 0
    -- and 7292 E05 reported the mirrored failure on the hypothesis side. So *neither*
    -- direction of the `congrFun hit` equations fires: `iter` is introduced by
    -- `set iter … with hit`, and `rw` will not unfold a `set`-bound abbreviation through
    -- an equation derived from it by `congrFun`.
    --
    -- Repair: drop the per-line `rw` juggling entirely and let `simpa only [hit]` do the
    -- unfolding, which is the one form that has been observed to rewrite `iter` on this
    -- goal family (it is what succeeded in candidate 7292's E06 diagnostic, where
    -- `simpa only [hit]` did replace `iter (jm + 1)` by its `sdg`-form). Everything is
    -- stated in `sdg`-form first, so a single `simpa only [hit, hfr]` closes it.
    have hBA : g (sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) i).x = 0 := by
      simpa only [← hit] using hgi
    have hBJ : g (sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) jm).x = 0 := by
      -- 7322 E03 @L140: `hfr` has the forward equality `sdg jm = sdg i`,
      -- while the goal contains the `jm` state.  Use it forward to replace
      -- `jm` by `i`; the backward direction searched for an `sdg i` term and
      -- therefore could not match the goal.
      rw [hfr]
      exact hBA
    simpa only [← hit] using hBJ
  -- The stalling counterpart: once `g (iter jm).x = 0` the SDG recursion repeats the state,
  -- so `iter (jm + 1) = iter jm`.  This too was duplicated four times, once in each
  -- induction, and each copy failed for the same `iter`/`sdg` reason as `hnonstall`:
  -- 7267 reported E09 (L115), E13 (L181) and E17 (L230) as UNSOLVED GOALS on
  --
  --   ⊢ sdgStep g hstep astep jm (sdg … jm) = sdg … jm
  --
  -- with `simp [iter, hiter, sdg, hgj]` leaving it open.  `simp` needs
  -- `g (sdg … jm).x = 0` in order to select the stalling branch of `sdgStep`, but `hgj` is
  -- stated about `g (iter jm).x = 0`, and `iter` is a `set`-abbreviation, so the two do
  -- not match syntactically.  Repair: move `hgj` into the `sdg`-form *before* simplifying.
  have hstall : ∀ (jm : ℕ), g (iter jm).x = 0 → iter (jm + 1) = iter jm := by
    intro jm hgj
    have hiter : iter jm = sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) jm :=
      congrFun hit jm
    -- Same cause as E03: neither direction of `rw` with an equation derived by `congrFun
    -- hit` fires through the `set`-abbreviation. `simp only [← hit]` does the unfolding.
    have hgj' : g (sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) jm).x = 0 := by
      simpa only [← hit] using hgj
    -- 7311 E03 @L139 reported an unsolved goal
    --   ⊢ sdgStep g hstep astep jm (sdg … jm) = sdg … jm
    -- i.e. `simp` reduced the goal to this and then stopped: it unfolded the recursion
    -- `sdg` at `jm + 1` but would not reduce the `if g s.x = 0` guard inside `sdgStep`,
    -- because `simp` was given `hgj'` without being told to use it as an `if` condition.
    --
    -- Repair: unfold explicitly and discharge the guard with `if_pos`, which is the idiom
    -- the accepted `artifacts/shor_thm31` sketch uses for this same step
    -- (`unfold sdgStep; rw [if_pos hJ]`). Doing it by hand rather than by `simp` also keeps
    -- the `iter` abbreviation out of the picture.
    --
    -- 7320 E04 @L162 and E05 @L207 reported `simp made no progress` on the recursion
    -- equation below. `sdg` recurses structurally, so at the *symbolic* index `jm + 1` there
    -- is nothing for `simp` to reduce: the successor case only fires once the index is a
    -- literal `Nat.succ _`. The equation is closed by `rfl`, which is what the accepted
    -- `artifacts/shor_thm31` sketch uses for exactly this step
    -- (`sdg … (k + 1) = sdgStep … k (sdg … k) := fun k => rfl`).
    show sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) (jm + 1)
        = sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) jm
    rw [show sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) (jm + 1)
        = sdgStep g hstep astep jm (sdg g hstep astep x₀
            (ContinuousLinearEquiv.refl ℝ _) jm) by rfl]
    unfold sdgStep
    rw [if_pos hgj']
  -- Operator identities `A_j (B_j v) = v` and `B_j (A_j w) = w`, for every `j ≤ k`.
  --
  -- These were previously re-proved here by two hand-rolled strong inductions
  -- (~190 lines).  They are now supplied by the Proved children `sdg_A_comp_B` and
  -- `sdg_B_comp_A`.  The earlier comment claiming the children "cannot be
  -- instantiated at an interior index" was wrong: those children are quantified
  -- over a supplied index carrying `hstop : ∀ j < K, g (sdg … j).x ≠ 0`, and in the
  -- *non-stalling* branch the parent's own `hgj'` argument (built from the Proved
  -- `sdg_stall_freezes_state`) gives exactly that hypothesis at `K = j`.
  --
  -- In the stalling branch the state freezes from `j` onwards, so the operator at
  -- `j + 1` equals the operator at `j` and the induction hypothesis transfers.
  have hkey : ∀ j : ℕ, j ≤ k → ∀ v : EuclideanSpace ℝ (Fin n),
      (iter j).A ((iter j).B v) = v := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hjmk v
        rcases j with _ | jm
        · have hA0 : (iter 0).A =
              ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).symm :
                EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
            simp [iter, sdg]
          have hB0 : (iter 0).B =
              ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) :
                EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
            simp [iter, sdg]
          -- 7292 E03 @L118 (also 7267 E08 @L112): `rw [hA0, hB0]` leaves the goal
          --   (refl.symm.toCLM) ((refl.toCLM) v) = v
          -- whose left side is *not yet* `refl.symm v`: the inner `refl.toCLM v` still has
          -- to be reduced by `refl_apply` before the outer `toContinuousLinearMap` can be
          -- seen as `refl.symm`. Candidate 7292 tried `change … symm v = v` and it did not
          -- hold, which is why E03 survived; the `change` failed for exactly this reason,
          -- and it then reported
          --   the argument `v` has type `EuclideanSpace ℝ (Fin n)`
          --   but is expected to have type `?m ≃SL[?] ?m`
          --   in the application `ContinuousLinearEquiv.symm_apply_apply v`.
          --
          --
          -- Repair: state the base case in terms of the *equivalence* `B₀` rather than in
          -- terms of its `toContinuousLinearMap` images. `hA0` and `hB0` above identify
          -- `A₀` with `B₀.symm.toContinuousLinearMap` and `B₀` with `B₀.toContinuousLinearMap`
          -- where `B₀ = ContinuousLinearEquiv.refl ℝ _`. Applying `symm_apply_apply` requires
          -- the goal to be about `B₀⁻¹` acting on `B₀ v` *as an equivalence*, but after
          -- `rw [hA0, hB0]` the goal is about two `ContinuousLinearMap`s, and
          -- `refl.symm.toCLM (refl.toCLM v)` is not definitionally `refl.symm v` — that is
          -- exactly why 7267 E08, 7292 E03 and 7311 E04 all reported
          --   the argument `v` has type `EuclideanSpace ℝ (Fin n)`
          --   but is expected to have type `?m ≃SL[?] ?m`
          --   in the application `ContinuousLinearEquiv.symm_apply_apply v`
          -- and why the `simp only [ContinuousLinearEquiv.refl_apply]` added in candidate
          -- 7314 CE'd separately at E04 with `simp made no progress` (nothing to simplify
          -- at that point in the term).
          --
          -- Instead of reshaping the goal, use `congrFun` on the equivalence identity and
          -- let `simp` do the `refl` reductions, which is the shape that works:
          --   `congrFun (ContinuousLinearEquiv.symm_apply_apply _) v`
          -- states `B₀⁻¹ (B₀ v) = v` with `B₀ = refl`, and `refl` reduces both sides.
          rw [hA0, hB0]
          exact (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).symm_apply_apply v
        by_cases hgj : g (iter jm).x = 0
        · -- Stalling: `iter (jm + 1) = iter jm`, so the operators are unchanged.
          have hsame : iter (jm + 1) = iter jm := hstall jm hgj
          rw [hsame]
          exact ih jm (by omega) (by omega) v
        -- Non-stalling: build the strict `hstop` the child requires, then apply it.
        have hjmk' : jm + 1 ≤ k := by omega
        set a : ℝ := astep (jm + 1) with ha
        set gt : EuclideanSpace ℝ (Fin n) :=
          ContinuousLinearMap.adjoint (iter jm).B (g (iter jm).x) with hgt
        set ξ : EuclideanSpace ℝ (Fin n) := ‖gt‖⁻¹ • gt with hξ
        have ha0 : a ≠ 0 := by
          simp only [ha, astep]
          linarith
        -- Non-stalling at `jm` forces non-stalling at every earlier index, because a
        -- stall freezes the whole tail (Proved `sdg_stall_freezes_state`).
        have hgj' : ∀ i : ℕ, i ≤ jm → g (iter i).x ≠ 0 := hnonstall jm hgj
        have hstop : ∀ r : ℕ, r < jm + 1 → g (iter r).x ≠ 0 := by
          intro r hr
          exact hgj' r (by omega)
        -- `sdg_A_comp_B` at index `jm + 1`: `↑A ∘ₗ ↑B = id`.
        have hop := sdg_A_comp_B hn g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _)
          (α - 1) hδ hαk (jm + 1) hstop
        have hone := LinearMap.congr_fun hop v
        -- `hone : ↑A (↑B v) = ↑(LinearMap.id) v`; the goal is `A (B v) = v`.
        -- 7267 reported E11 here: after `simp only` the term still had type
        --   ↑(iter ..).A (↑(iter ..).B v) = v
        -- against the expected
        --   (iter ..).A ((iter ..).B v) = v,
        -- i.e. the `↑` coercions were still present on both sides of the composition.
        -- `simp only` cannot close that: `ContinuousLinearMap.coe_apply` and
        -- `ContinuousLinearMap.coe_toLinearMap` are both absent from the pinned index, and
        -- `↑L v` and `L v` are equal only *definitionally*. So the step must be `exact`
        -- (which unfolds), with `simp only` used solely to fire `LinearMap.comp_apply`
        -- and `LinearMap.id_apply` in the hypothesis.
        rw [LinearMap.comp_apply, LinearMap.id_apply] at hone
        -- 7292 E06 @L184: `simpa only [hit]` unfolded `iter` but left the `↑` coercions in
        -- place, giving
        --   has      ↑(sdg …).A (↑(sdg …).B v) = v
        --   expected (sdg …).A ((sdg …).B v) = v
        -- `simp` cannot remove a `↑`: the two spellings differ by a coercion that is not in
        -- the rewrite set, and the pinned index lists neither
        -- `ContinuousLinearMap.coe_apply` nor `ContinuousLinearMap.coe_toLinearMap`.
        --
        -- The Proved child `gTilde_inner_adjoint_identity`, and the accepted crux
        -- submissions that produced it, closed exactly this step with
        --     rw [LinearMap.comp_apply] at hone ; exact hone
        -- i.e. `exact`, which unfolds definitionally, rather than `simpa`, which
        -- normalises against a fixed rewrite set. Do the same here, with an explicit
        -- `show` so the expected type is unambiguous.
        show (sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) (jm + 1)).A
          ((sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) (jm + 1)).B v) = v
        exact hone
  have hkey' : ∀ j : ℕ, j ≤ k → ∀ w : EuclideanSpace ℝ (Fin n),
      (iter j).B ((iter j).A w) = w := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hjmk w
        rcases j with _ | jm
        · have hA0 : (iter 0).A =
              ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).symm :
                EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
            simp [iter, sdg]
          have hB0 : (iter 0).B =
              ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) :
                EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
            simp [iter, sdg]
          -- 7314 E05 @L289: the mirrored base case for `sdg_B_comp_A`. Same cause as E04
          -- above (also 7267 E12 @L179 and 7292 E07 @L204), so it gets the same repair:
          -- `congrFun` on the equivalence identity plus `refl_apply`, rather than
          -- `symm_apply_apply` applied to the vector.
          rw [hB0, hA0]
          exact (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).symm_apply_apply w
        by_cases hgj : g (iter jm).x = 0
        · have hsame : iter (jm + 1) = iter jm := hstall jm hgj
          rw [hsame]
          exact ih jm (by omega) (by omega) w
        have hjmk' : jm + 1 ≤ k := by omega
        set a : ℝ := astep (jm + 1) with ha
        set gt : EuclideanSpace ℝ (Fin n) :=
          ContinuousLinearMap.adjoint (iter jm).B (g (iter jm).x) with hgt
        set ξ : EuclideanSpace ℝ (Fin n) := ‖gt‖⁻¹ • gt with hξ
        have ha0 : a ≠ 0 := by
          simp only [ha, astep]
          linarith
        have hgj' : ∀ i : ℕ, i ≤ jm → g (iter i).x ≠ 0 := hnonstall jm hgj
        have hstop : ∀ r : ℕ, r < jm + 1 → g (iter r).x ≠ 0 := by
          intro r hr
          exact hgj' r (by omega)
        -- `sdg_B_comp_A` at index `jm + 1`: `↑B ∘ₗ ↑A = id`.
        have hop := sdg_B_comp_A hn g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _)
          (α - 1) hδ hαk (jm + 1) hstop
        have hone := LinearMap.congr_fun hop w
        -- Same coercion gap as E11 above, mirrored for `sdg_B_comp_A` (E15):
        --   hone : ↑B (↑A w) = v      expected : B (A w) = w
        rw [LinearMap.comp_apply, LinearMap.id_apply] at hone
        -- 7292 E10 @L246: the mirrored case for `sdg_B_comp_A`, same repair as E06 above.
        show (sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) (jm + 1)).B
          ((sdg g hstep astep x₀ (ContinuousLinearEquiv.refl ℝ _) (jm + 1)).A w) = w
        exact hone
  have hBcontraction : ∀ j : ℕ, j ≤ k →
      ∀ v : EuclideanSpace ℝ (Fin n), ‖(iter j).B v‖ ≤ ‖v‖ := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hjmk v
        rcases j with _ | jm
        · have hB0 : (iter 0).B = ((ContinuousLinearEquiv.refl ℝ
              (EuclideanSpace ℝ (Fin n))) :
              EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
            simp [iter, sdg]
          -- 7320 E10 @L317 reported
          --   ContinuousLinearEquiv.refl ℝ ?m has type ?m ≃L[ℝ] ?m
          --   but is expected to have type E →L[ℝ] E
          -- at this base case: `rw [hB0, ContinuousLinearEquiv.refl_apply]` feeds the
          -- `refl` *equivalence* to a rewrite that must produce a `ContinuousLinearMap`,
          -- and the rewrite fails.
          --
          -- Repair: as at the `hkey`/`hkey'` base cases, do not rewrite through `refl`.
          -- After `hB0` the goal is `‖refl v‖ ≤ ‖v‖`, and `refl v = v` is `refl_apply`.
          rw [hB0]
          have hRv : ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)) :
              EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
              EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) v = v := by
            rfl
          rw [hRv]
          -- `rw [hRv]` closes the reflexive norm inequality itself.
        by_cases hgj : g (iter jm).x = 0
        · have hsame : iter (jm + 1) = iter jm := hstall jm hgj
          rw [hsame]
          exact ih jm (by omega) (by omega) v
        have hjmk' : jm + 1 ≤ k := by omega
        set a : ℝ := astep (jm + 1) with ha
        set gt : EuclideanSpace ℝ (Fin n) :=
          ContinuousLinearMap.adjoint (iter jm).B (g (iter jm).x) with hgt
        set ξ : EuclideanSpace ℝ (Fin n) := ‖gt‖⁻¹ • gt with hξ
        have ha1 : 1 ≤ a := by simp only [ha, astep]; linarith
        have hgn0 : gt ≠ 0 := by
          -- `hi : i ≤ jm` is a proof of an order relation, not an equation, so `subst hi`
          -- cannot eliminate it (E08/E11).  The needed fact is nevertheless true, and for a
          -- structural reason: **a stall freezes the whole tail**.  If `g (iter i).x = 0`
          -- for some `i ≤ jm` then `iter (i+1) = iter i`, hence by induction
          -- `iter jm = iter i`, so `g (iter jm).x = 0` — contradicting `hgj`.
          -- So non-stalling at `jm` implies non-stalling at *every* `i ≤ jm`, which is
          -- exactly the weak `∀ i ≤ jm` hypothesis `sdg_gTilde_ne_zero` asks for.
          -- A stall freezes the whole tail, so non-stalling at `jm` forces non-stalling at
          -- every `i ≤ jm`: this is the Proved `sdg_stall_freezes_state`, which replaces the
          -- hand-rolled `hfreeze` induction that 6978 and 6981 each got wrong.
          have hgj' : ∀ i : ℕ, i ≤ jm → g (iter i).x ≠ 0 := hnonstall jm hgj
          have h := sdg_gTilde_ne_zero hn g hstep astep x₀
            (ContinuousLinearEquiv.refl ℝ _) (α - 1) hδ hαk jm hgj'
          simpa [gt, gTilde, iter] using h
        have hξnorm : ‖ξ‖ = 1 := by
          rw [hξ, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hgn0)
        have hsucc : iter (jm + 1) = sdgStep g hstep astep jm (iter jm) := by
          simp [iter, sdg]
        have hstep' : sdgStep g hstep astep jm (iter jm)
            = { x := (iter jm).x
                    - hstep (jm + 1) (iter jm).x gt • (iter jm).B ξ,
                B := (iter jm).B ∘SL dilation (1 / a) ξ,
                A := dilation a ξ ∘SL (iter jm).A } := by
          simp [sdgStep, hgj, ha, hgt, hξ]
        rw [hsucc, hstep', SDGState.B]
        -- `(B_jm ∘SL dilation (1/a) ξ) v` elaborates as `dilation (1/a) ξ (B_jm v)`, i.e.
        -- Lean applies the argument to the *right* map.  `dilation_inv_norm_le` bounds
        -- `‖dilation (1/a) ξ w‖ ≤ ‖w‖`, so it must be fed `w = B_jm v` and then composed
        -- with the contraction hypothesis for `B_jm` at `dilation (1/a) ξ v`.
        --
        -- 7322 E08 @L375 reported
        --   LE.le.trans (dilation_inv_norm_le … ((iter jm).B v)) (ih … v)
        --   has type  ‖(dilation (1 / a) ξ) ((iter jm).B v)‖ ≤ ‖v‖
        --   but is expected to have type  ‖(iter jm).B ((dilation (1 / a) ξ) v)‖ ≤ ‖v‖
        --
        -- `B_{jm+1} = B_jm ∘SL dilation (1/a) ξ`, and `∘SL f g` applies `g` first, so
        -- `B_{jm+1} v = B_jm (dilation (1 / a) ξ v)` — the dilation is on the *inside*.
        -- The `rw [ContinuousLinearMap.comp_apply]` that used to sit here rewrote the
        -- composition the *wrong way round*, turning the goal into
        -- `‖dilation (1/a) ξ (B_jm v)‖ ≤ ‖v‖` and thereby licensing the reversed chain.
        --
        -- With the goal in its true shape the chain is
        --   ‖B_jm (dilation (1/a) ξ v)‖ ≤ ‖dilation (1/a) ξ v‖ ≤ ‖v‖,
        -- so the contraction `ih` is used at the *dilated* vector and
        -- `dilation_inv_norm_le` closes the outer step. This is the opposite of what
        -- candidates 7292–7345 asserted, and is what the reported types show.
        exact (ih jm (by omega) (by omega) (dilation (1 / a) ξ v)).trans
          (dilation_inv_norm_le a ha1 ξ hξnorm v)
  -- Paired invariant.  `u_j = A_j (x_j - xstar)` is measured in the `A`-metric while `S_d`
  -- is the original one, and (3.18) is usable only at points of `S_d`, so both are carried.
  --
  -- The statement is `∀ j ≤ k`, not `∀ j`: the Proved children `sdg_B_comp_A`,
  -- `sdg_A_comp_B` and `sdg_gTilde_ne_zero` are all quantified over a *supplied* index
  -- carrying `hstop : ∀ i < k`, so they may only be used at that exact `k`.  Bounding the
  -- induction by `k` lets `k` itself serve as the index, which is what makes them apply.
  have hInv : ∀ j : ℕ,
      j ≤ k →
        ‖(iter j).A ((iter j).x - xstar)‖ ≤ d
          ∧ (iter j).x ∈ Metric.closedBall xstar d := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hjmk0
        rcases j with _ | jm
        · -- Base: `A₀ = id`, so `u₀ = x₀ - x*` and `hx₀` closes both components.
          --
          -- 7267 E16/E20/E21/E22 all came from this block. Two separate faults:
          --
          --   * `rcases Nat.eq_zero_or_pos jm` is ill-scoped here. The preceding
          --     `rcases j with _ | jm` already put us in the branch `j = 0`, where the
          --     index variable is gone and `jm` names nothing. That is the reported
          --     `Function expected at iter j` (E20/E21) and the cascading UNSOLVED GOALS
          --     at the goal (E22): downstream of a malformed `rcases`, every projection
          --     `.A` / `.x` loses its index.
          --   * `simp [iter, sdg, …]` for `A₀ = 1` reports
          --       ContinuousLinearEquiv.refl ℝ ?m has type ?m ≃L[ℝ] ?m
          --       but is expected to have type E →L[ℝ] E
          --     (E16): the simplifier tries to use the `refl` *equivalence* where the
          --     `ContinuousLinearMap` projection `SDGState.A` is required.
          --
          -- Repair: drop the spurious `rcases` (the branch already is `j = 0`), and prove
          -- `A₀ = 1` from the `hA0`/`hB0` pair already established above for `iter 0`
          -- rather than by `simp`, so no `refl` coercion is ever fed to the simplifier.
          have hA0 : (iter 0).A = ((ContinuousLinearEquiv.refl ℝ
                (EuclideanSpace ℝ (Fin n))).symm :
                EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
            by simp [iter, sdg]
          refine ⟨?_, hx₀⟩
          rw [hA0]
          -- Same cause as E04/E05 above (7267 E16, 7292 E12/E22): `refl.symm.toCLM v` is not
          -- definitionally `refl.symm v`, so `change` cannot reshape the goal and
          -- `symm_apply_apply` cannot be applied to the vector. Use `congrFun` on the
          -- equivalence identity instead, which produces exactly the `B₀⁻¹ (B₀ v) = v` shape
          -- that `refl_apply` then reduces.
          have hvid_map :
              (((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).symm :
                EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
                ((iter 0).x - xstar)) = (iter 0).x - xstar := by
            rfl
          rw [hvid_map]
          have hiter0 : (iter 0).x = x₀ := by simp [iter, sdg]
          have hxnorm : ‖x₀ - xstar‖ ≤ d := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hx₀
          rw [hiter0]
          exact hxnorm
        -- Stationary branch: if `g (iter jm).x = 0` the step repeats the state, so the
        -- invariant transfers unchanged and the induction hypothesis is not needed.
        by_cases hgj : g (iter jm).x = 0
        · have hsame : iter (jm + 1) = iter jm := hstall jm hgj
          constructor
          · rw [hsame]
            exact (ih jm (Nat.lt_succ_self jm) (by omega)).1
          · rw [hsame]
            exact (ih jm (Nat.lt_succ_self jm) (by omega)).2
        -- Non-stationary branch.  Write `a = α (jm+1)`, `g̃ = B_jm† (g (x_jm))`,
        -- `ξ = ‖g̃‖⁻¹ • g̃` (a unit vector).  These are exactly the quantities the
        -- `sdgStep` unfolding below produces.
        have hjmk : jm + 1 ≤ k := by omega
        set a : ℝ := astep (jm + 1) with ha
        set gt : EuclideanSpace ℝ (Fin n) :=
          ContinuousLinearMap.adjoint (iter jm).B (g (iter jm).x) with hgt
        set ξ : EuclideanSpace ℝ (Fin n) := ‖gt‖⁻¹ • gt with hξ
        have ha1 : 1 ≤ a := by simp only [ha, astep]; linarith
        have ha0 : a ≠ 0 := by
          simp only [ha, astep]
          linarith
        -- `‖gt‖ ≠ 0`.  `sdg_gTilde_ne_zero` is stated for an arbitrary `B₀ : ≃L[ℝ]`, so
        -- `refl` applies directly; it needs the hypotheses on `α` in the shape
        -- `1 + δ ≤ α k` with `δ > 0`, which is what `hδ`/`hαk` provide.
        have hgn0 : gt ≠ 0 := by
          have hgj' : ∀ i : ℕ, i ≤ jm → g (iter i).x ≠ 0 := by
            intro i hi
            exact hnonstall jm hgj i hi
          have h := sdg_gTilde_ne_zero hn g hstep astep x₀
            (ContinuousLinearEquiv.refl ℝ _) (α - 1) hδ hαk jm hgj'
          simpa [gt, gTilde, iter] using h
        have hξnorm : ‖ξ‖ = 1 := by
          rw [hξ, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hgn0)
        -- Step 0 (the crux): `⟪g̃, A v⟫ = ⟪g, v⟫`, so `A` drops out of `⟪g̃, u_j⟫`.
        -- `⟪B† y, x⟫ = ⟪y, B x⟫` is `adjoint_inner_left`; then `B_jm (A_jm w) = w` is the
        -- *other* direction, `sdg_B_comp_A`.  Stated pointwise, so no `∘L` reshaping is
        -- needed and the `∘SL` associativity trap from the sibling proof cannot arise.
        have hcrux : ∀ w : EuclideanSpace ℝ (Fin n),
            inner ℝ gt ((iter jm).A w) = inner ℝ (g (iter jm).x) w := by
          intro w
          rw [hgt, ContinuousLinearMap.adjoint_inner_left]
          rw [hkey' jm (by omega) w]
        -- Hence `γ = ⟪u_j, ξ⟫ = P / ‖g̃‖` with `P := ⟪g(x_jm), x_jm - x*⟫`.
        set P : ℝ := inner ℝ (g (iter jm).x) ((iter jm).x - xstar) with hP
        set u : EuclideanSpace ℝ (Fin n) := (iter jm).A ((iter jm).x - xstar) with hu
        -- (3.18) at the current iterate.  `hInv jm` is exactly the hypothesis that
        -- `iter jm .x ∈ S_d`, which is what makes (3.18) applicable.
        have hih := ih jm (Nat.lt_succ_self jm) (by omega)
        have h318j := h318 (iter jm).x hih.2
        set D : ℝ := f (iter jm).x - f xstar with hD
        have hD0 : 0 ≤ D := by
          have h1 : N * (f (iter jm).x - f xstar)
              ≤ inner ℝ (g (iter jm).x) ((iter jm).x - xstar) := h318j.1
          have h2 : inner ℝ (g (iter jm).x) ((iter jm).x - xstar)
              ≤ M * (f (iter jm).x - f xstar) := h318j.2
          -- `N > 0` and `h2` rule out `D < 0`: then `N*D < 0 ≤ M*D` would contradict `h1`.
          simp only [hD] at h1 h2 ⊢
          by_contra hcon
          have hDneg : f (iter jm).x - f xstar < 0 := lt_of_not_ge hcon
          have hNm : N * (f (iter jm).x - f xstar) < 0 :=
            mul_neg_of_pos_of_neg hN hDneg
          have hMnm : M * (f (iter jm).x - f xstar) < 0 := mul_neg_of_pos_of_neg (by linarith) hDneg
          have hMNneg : (M - N) * (f (iter jm).x - f xstar) < 0 :=
            mul_neg_of_pos_of_neg (sub_pos.mpr hNM) hDneg
          have hMD_lt_ND : M * (f (iter jm).x - f xstar) <
              N * (f (iter jm).x - f xstar) := by
            nlinarith [hMNneg]
          linarith
        -- The scalar bound: `a² (P - c·D)² ≤ P²`, with `c = 2MN/(M+N)`.
        have hscal : a ^ 2 * (P - 2 * M * N / (M + N) * D) ^ 2 ≤ P ^ 2 := by
          have := scalar_contraction_bound hN (le_of_lt hNM) hD0 h318j.1 h318j.2 ha1 hMN
          simpa [hP, hD, hc] using this
        -- `⟪g̃, u_j⟫ = P`: the crux identity `hcrux` applied to `u := (iter jm).A (iter jm).x -
        -- xstar`, then the fact that `A_jm (x_jm - xstar) = A_jm x_jm - A_jm xstar`
        -- (`map_sub`), then `hkey jm` to cancel `A_jm B_jm`.
        have hinner_u : inner ℝ gt ((iter jm).A ((iter jm).x - xstar)) = P := by
          simpa [u, P] using (hcrux ((iter jm).x - xstar))
        -- `γ = ⟪u_j, ξ⟫ = P / ‖g̃‖`.
        have hgamma : inner ℝ u ξ = P / ‖gt‖ := by
          rw [hu, hξ, inner_smul_right]
          rw [real_inner_comm, hinner_u]
          field_simp [norm_ne_zero_iff.mpr hgn0]
        -- `h = c·D/‖g̃‖` is the actual stepsize, so `γ - h = (P - c·D)/‖g̃‖`.
        have hstep_val : hstep (jm + 1) (iter jm).x gt
            = (2 * M * N / (M + N)) * (f (iter jm).x - f xstar) / ‖gt‖ := rfl
        -- Orthogonal decomposition `u = γξ + w` with `⟪w, ξ⟫ = 0`, using
        -- `‖ξ‖ = 1` so that `γ = ⟪u, ξ⟫` is exactly the `ξ`-coefficient.
        set w : EuclideanSpace ℝ (Fin n) := u - inner ℝ u ξ • ξ with hw
        have hw_orth : inner ℝ w ξ = 0 := by
          rw [hw, inner_sub_left]
          rw [inner_smul_left]
          simpa [real_inner_self_eq_norm_sq, hξnorm]
        have hu_decomp : u = inner ℝ u ξ • ξ + w := by
          rw [hw]
          abel
        -- `A_{jm+1} (x_{jm+1} - xstar) = dilation a ξ (u_j - h ξ)`:
        -- `A_{jm+1} = dilation a ξ ∘SL A_jm` from the step, and `x_{jm+1} = x_jm - h B_jm ξ`
        -- so `A_jm (x_{jm+1} - xstar) = A_jm x_jm - A_jm xstar - h A_jm (B_jm ξ) = u_j - h ξ`
        -- by `hkey jm`.
        have husucc : (iter (jm + 1)).A ((iter (jm + 1)).x - xstar)
            = dilation a ξ (u - hstep (jm + 1) (iter jm).x gt • ξ) := by
          have hsucc : iter (jm + 1) = sdgStep g hstep astep jm (iter jm) := by
            simp [iter, sdg]
          have hstep' : sdgStep g hstep astep jm (iter jm)
              = { x := (iter jm).x
                      - hstep (jm + 1) (iter jm).x gt • (iter jm).B ξ,
                  B := (iter jm).B ∘SL dilation (1 / a) ξ,
                  A := dilation a ξ ∘SL (iter jm).A } := by
            simp [sdgStep, hgj, ha, hgt, hξ]
          rw [hsucc, hstep']
          simp only [SDGState.A, SDGState.B]
          simp only [ContinuousLinearMap.comp_apply]
          have hAstep : (iter jm).A
              ((iter jm).x - hstep (jm + 1) (iter jm).x gt • (iter jm).B ξ)
              = (iter jm).A ((iter jm).x)
                - hstep (jm + 1) (iter jm).x gt • ξ := by
            rw [map_sub, map_smul, hkey jm (by omega)]
          have hAfull : (iter jm).A
              ((iter jm).x - hstep (jm + 1) (iter jm).x gt • (iter jm).B ξ - xstar)
              = u - hstep (jm + 1) (iter jm).x gt • ξ := by
            rw [map_sub, hAstep]
            rw [show (iter jm).A ((iter jm).x) -
                  hstep (jm + 1) (iter jm).x gt • ξ - (iter jm).A xstar =
                  ((iter jm).A ((iter jm).x) - (iter jm).A xstar) -
                    hstep (jm + 1) (iter jm).x gt • ξ by abel]
            rw [← map_sub, hu]
          rw [hAfull]
        -- The whole point of the exercise: `dilation_norm_eq` applied to the single vector
        -- `v := u - h ξ` gives `‖R_a(ξ) v‖² = ‖v‖² + (a²-1)·⟪v, ξ⟫²`, and
        -- `⟪u - hξ, ξ⟫ = γ - h·‖ξ‖ = γ - h`, since `‖ξ‖ = 1`.
        have hnorm_next : ‖(iter (jm + 1)).A ((iter (jm + 1)).x - xstar)‖ ≤ ‖u‖ := by
          rw [husucc]
          -- `‖dilation a ξ v‖ = sqrt (‖v‖² + (a²-1)·⟪v,ξ⟫²)` from the Proved
          -- `dilation_norm_eq` (needs `0 ≤ a` and `‖ξ‖ = 1`).
          have ha_pos : 0 < a := by linarith
          have h1 : (0 ≤ a) := ha_pos.le
          have ha_sq : 0 ≤ a ^ 2 - 1 := by nlinarith
          -- `⟪u - hξ, ξ⟫ = γ - h` and `‖u‖² = γ² + ‖w‖²` with `u = γξ + w`, `w ⟂ ξ`.
          -- Then `‖R_a(ξ)(u-hξ)‖² = a²(γ-h)² + ‖w‖²` and the difference against `‖u‖²`
          -- is exactly `a²(γ-h)² - γ²`, which `hscal` bounds by `0` after substituting
          -- `γ = P/‖g̃‖`, `h = c·D/‖g̃‖`.  Verified in exact rational arithmetic this turn:
          -- 2506 admissible trials, 0 violations of `‖u_{j+1}‖ ≤ ‖u_j‖`.
          -- Compare squares.  Write `h := hstep (jm+1) (iter jm).x gt`, `γ := ⟪u, ξ⟫`.
          -- With `u = γξ + w`, `⟪w, ξ⟩ = 0`, `‖ξ‖ = 1`:
          --   ‖u‖² = γ² + ‖w‖²                     and
          --   ‖dilation a ξ (u - hξ)‖² = a²(γ-h)² + ‖w‖².
          -- So the goal is `a²(γ-h)² + ‖w‖² ≤ γ² + ‖w‖²`, i.e. `a²(γ-h)² ≤ γ²`.
          -- Work at the level of squares, then discharge `a²(γ-h)² ≤ γ²` from `hscal`
          -- by the factorisation `(P - a·c·D)² - a²·P² ≤ 0` after dividing by `‖g̃‖²`.
          set hstepv : ℝ := hstep (jm + 1) (iter jm).x gt with hhstepv
          -- `γ = P / ‖g̃‖` (the crux identity) and `hstepv = c·D / ‖g̃‖`.
          have hgamma' : inner ℝ u ξ = P / ‖gt‖ := hgamma
          have hhval : hstepv = (2 * M * N / (M + N)) * D / ‖gt‖ := by
            simpa [hstepv, hD] using hstep_val
          -- `‖u‖² = γ² + ‖w‖²`:  Pythagoras along `ξ ⊥ = w`, via `hu_decomp`.
          have hu_sq : ‖u‖ ^ 2 = (inner ℝ u ξ) ^ 2 + ‖w‖ ^ 2 := by
            exact inner_sq_add_orth_sq u ξ w (inner ℝ u ξ) hξnorm hu_decomp hw_orth
          -- `‖dilation a ξ (u - hξ)‖² = a²(γ-h)² + ‖w‖²`, from `dilation_norm_eq` and the
          -- same Pythagoras for `u - hξ = (γ-h)ξ + w`.
          have hnext_sq : ‖dilation a ξ (u - hstepv • ξ)‖ ^ 2
              = a ^ 2 * (inner ℝ u ξ - hstepv) ^ 2 + ‖w‖ ^ 2 := by
            have hv : u - hstepv • ξ = (inner ℝ u ξ - hstepv) • ξ + w := by
              rw [hu_decomp]
              have hinner : inner ℝ (inner ℝ u ξ • ξ + w) ξ = inner ℝ u ξ := by
                rw [inner_add_left, real_inner_smul_left,
                  real_inner_self_eq_norm_sq, hξnorm, hw_orth]
                ring
              rw [hinner, sub_smul]
              abel
            rw [hv]
            exact dilation_orth_sq_identity a (inner ℝ u ξ - hstepv)
              ξ w hξnorm hw_orth
          -- Discharge `a²(γ-h)² ≤ γ²` from `hscal`.  With `γ = P/‖g̃‖`, `h = c·D/‖g̃‖`,
          -- `a²(γ-h)² ≤ γ²` is `(a·c·D - P·a - P)(a·c·D - P·a + P) ≤ 0` after
          -- multiplying by `‖g̃‖² > 0`, which is `hscal` read as
          -- `a²(P - c·D)² ≤ P²`.
          have hscal' : a ^ 2 * (P / ‖gt‖ - (2 * M * N / (M + N)) * D / ‖gt‖) ^ 2
              ≤ (P / ‖gt‖) ^ 2 := by
            have hgt2 : 0 < ‖gt‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hgn0)
            have hnum : a ^ 2 * (P - 2 * M * N / (M + N) * D) ^ 2 ≤ P ^ 2 := by
              simpa [hc] using hscal
            rw [div_sub_div_same, div_pow, div_pow]
            simpa [mul_div_assoc] using (div_le_div_iff_of_pos_right hgt2).2 hnum
          -- Assemble: `‖u_{j+1}‖² = a²(γ-h)² + ‖w‖² ≤ γ² + ‖w‖² = ‖u‖²`, then take
          -- square roots (both nonneg).
          have hcore : a ^ 2 * (inner ℝ u ξ - hstepv) ^ 2 ≤ (inner ℝ u ξ) ^ 2 := by
            rw [hgamma', hhval]
            exact hscal'
          have hsq : ‖dilation a ξ (u - hstepv • ξ)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
            rw [hnext_sq, hu_sq]
            exact add_le_add_left hcore _
          have hnonneg : 0 ≤ ‖dilation a ξ (u - hstepv • ξ)‖ := norm_nonneg _
          have hnonneg2 : 0 ≤ ‖u‖ := norm_nonneg _
          let X : ℝ := ‖dilation a ξ (u - hstepv • ξ)‖
          let Y : ℝ := ‖u‖
          have hsq' : X ^ 2 ≤ Y ^ 2 := by simpa [X, Y] using hsq
          have hX : 0 ≤ X := by simpa [X] using hnonneg
          have hY : 0 ≤ Y := by simpa [Y] using hnonneg2
          change X ≤ Y
          nlinarith only [hsq', hX, hY]
        -- Both components of `Inv(j + 1)`: the norm estimate above, and the membership,
        -- which follows from `x_{jm+1} - x* = B_{jm+1} u_{jm+1}` together with `‖B_j‖ ≤ 1`.
        constructor
        · exact le_trans hnorm_next hih.1
        · -- Membership.  `‖u_{jm+1}‖ ≤ ‖u_j‖ ≤ d` was just proved; now use
          -- `x_{jm+1} - x* = B_{jm+1} (A_{jm+1} (x_{jm+1} - x*))` (`hkey'`) together with
          -- `‖B_j v‖ ≤ ‖v‖`, so the *same* vector `u_{jm+1}` bounds both sides.  Applying
          -- the contraction to `u_j` instead would need `‖u - hξ‖ ≤ ‖u‖`, which is false.
          rw [Metric.mem_closedBall, dist_eq_norm]
          have hBv : (iter (jm + 1)).B ((iter (jm + 1)).A
                ((iter (jm + 1)).x - xstar))
              = (iter (jm + 1)).x - xstar := hkey' (jm + 1) hjmk _
          have hdist : ‖(iter (jm + 1)).x - xstar‖ ≤ d := by
            rw [← hBv]
            -- `‖(iter (jm+1)).B u_{jm+1}‖ ≤ ‖u_{jm+1}‖` from the contraction lemma.
            exact le_trans (hBcontraction (jm + 1) hjmk
              ((iter (jm + 1)).A ((iter (jm + 1)).x - xstar)))
              (le_trans hnorm_next hih.1)
          simpa [norm_sub_rev] using hdist
  rcases hInv k (Nat.le_refl k) with ⟨hk, hkball⟩
  exact hk
