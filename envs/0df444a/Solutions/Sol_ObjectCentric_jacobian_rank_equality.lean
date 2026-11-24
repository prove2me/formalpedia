-- Prove2me | solution 1 for ObjectCentric.jacobian_rank_equality
-- status  : ACCEPTED   (prove)
-- author  : @fangshuming
-- created : 2026-11-24T14:57:19.303084+00:00
-- url     : https://prove2.me/submissions/9ee0a637-96f3-43ed-a27f-4173839c785f

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open ObjectCentric
open scoped Topology
open Matrix

namespace LocalHelpers

open scoped BigOperators
open Finset

lemma indicator_single_eq {K M : ℕ} (b : Fin K × Fin M) :
  (fun (j : Fin K) (m : Fin M) => if j = b.1 ∧ m = b.2 then (1 : ℝ) else 0)
  = Pi.single b.1 (Pi.single b.2 (1 : ℝ)) := by
  funext j m
  classical
  by_cases hj : j = b.1
  · subst hj
    by_cases hm : m = b.2
    · subst hm; simp [Pi.single]
    · simp [Pi.single, hm]
  · simp [Pi.single, hj]

lemma map_univ_sum_smul
  {ι : Type} [Fintype ι]
  {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (ψ : E →L[ℝ] F) (a : ι → ℝ) (v : ι → E) :
  ψ (∑ i, a i • v i) = ∑ i, a i • ψ (v i) := by
  classical
  simpa [map_smul] using
    (ContinuousLinearMap.map_sum ψ (fun i => a i • v i) (Finset.univ))

end LocalHelpers

namespace LinearBridge

set_option autoImplicit false

-- Short aliases
abbrev Lat (K M : ℕ) := ObjectCentric.Lat K M
abbrev Obs (N : ℕ) := ObjectCentric.Obs N
abbrev Pair (K M : ℕ) := (Fin K × Fin M) → ℝ

-- Linear maps between curried and uncurried function spaces
noncomputable def curryLM (K M : ℕ) :
  Lat K M →ₗ[ℝ] Pair K M :=
{ toFun := fun x => fun p => x p.1 p.2
  map_add' := by intro x y; funext p; rfl
  map_smul' := by intro a x; funext p; rfl }

noncomputable def uncurryLM (K M : ℕ) :
  Pair K M →ₗ[ℝ] Lat K M :=
{ toFun := fun y => fun k m => y (k, m)
  map_add' := by intro y₁ y₂; funext k m; rfl
  map_smul' := by intro a y; funext k m; rfl }

-- Linear projection that picks only coordinates indexed by a finite set S ⊆ Fin N
noncomputable def projS {N : ℕ} (S : Set (Fin N)) : Obs N →ₗ[ℝ] (S → ℝ) where
  toFun := fun y s => y (s : Fin N)
  map_add' := by intro y₁ y₂; funext s; simp
  map_smul' := by intro a y; funext s; simp

-- Pointwise: nested single equals pair single evaluated on `(k,m)`.
lemma nested_eval_eq_pair_eval
  {K M : ℕ} (c : Fin K × Fin M) (k : Fin K) (m : Fin M) :
  ((Pi.single (M := fun _ : Fin K => (Fin M → ℝ)) c.1
      (Pi.single (M := fun _ : Fin M => ℝ) c.2 (1 : ℝ))) k) m
    = (Pi.single (M := fun _ : Fin K × Fin M => ℝ) c (1 : ℝ)) (k, m) := by
  classical
  by_cases hk : k = c.1
  · by_cases hm : m = c.2
    · subst hk; subst hm; simp [Pi.single_apply]
    · subst hk
      have hpair : (c.1, m) ≠ c := by
        intro h; exact hm ((Prod.ext_iff.mp h).2)
      simp [Pi.single_apply, hpair, hm, Prod.mk.injEq]
  ·
    have hpair : (k, m) ≠ c := by
      intro h; exact hk ((Prod.ext_iff.mp h).1)
    simp [Pi.single_apply, hpair, hk, Prod.mk.injEq]

-- Uncurry of the standard pair basis equals the official nested latent basis (pointwise form).
lemma uncurry_basisFun_eq_nested'
  (K M : ℕ) (c : Fin K × Fin M) :
  (uncurryLM K M) ((Pi.basisFun ℝ (Fin K × Fin M)) c)
    = (Pi.single (M := fun _ : Fin K => (Fin M → ℝ)) c.1
        (Pi.single (M := fun _ : Fin M => ℝ) c.2 (1 : ℝ))) := by
  classical
  funext k m
  simpa [uncurryLM, Pi.basisFun_apply] using
    (nested_eval_eq_pair_eval (K := K) (M := M) c k m).symm

-- The nested basis vector equals `uncurryLM` of the pair single.
lemma nested_eq_uncurry_single
  (K M : ℕ) (c : Fin K × Fin M) :
  (fun k m =>
    ((Pi.single (M := fun _ : Fin K => (Fin M → ℝ)) c.1
      (Pi.single (M := fun _ : Fin M => ℝ) c.2 (1 : ℝ))) k) m)
    = (uncurryLM K M) (Pi.single (M := fun _ : Fin K × Fin M => ℝ) c (1 : ℝ)) := by
  classical
  funext k m
  simpa [uncurryLM] using
    (nested_eval_eq_pair_eval (K := K) (M := M) c k m)

-- Bridge: the official `jac` submatrix equals the matrix of the linear map
-- `projS S ∘ (fderiv f z).toLinearMap ∘ uncurryLM` with respect to the standard Pi bases.
lemma jac_submatrix_eq_toMatrix_comp
  (K M N : ℕ) (f : Lat K M → Obs N) (z : Lat K M) (S : Set (Fin N)) :
  (ObjectCentric.jac f z).submatrix (fun s : S => (s : Fin N)) id
    = LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) (Pi.basisFun ℝ S)
        ((projS S) ∘ₗ (fderiv ℝ f z).toLinearMap ∘ₗ (uncurryLM K M)) := by
  classical
  ext s c
  simp [Matrix.submatrix, LinearMap.toMatrix_apply, projS,
        LinearMap.comp_apply, uncurry_basisFun_eq_nested', nested_eq_uncurry_single,
        ObjectCentric.jac, Pi.basisFun_repr]

-- Identities for curry/uncurry as mutual inverses (on the nose)
lemma comp_curry_uncurry_id_pair (K M : ℕ) :
  (curryLM K M).comp (uncurryLM K M) = LinearMap.id := by
  ext p q
  rfl

lemma comp_uncurry_curry_id_lat (K M : ℕ) :
  (uncurryLM K M).comp (curryLM K M) = LinearMap.id := by
  ext z k m
  rfl

end LinearBridge

set_option autoImplicit false

/-- Top-level solution for Lemma 4: jacobian_rank_equality. -/
 theorem solution {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (fhat : Lat K M → Obs N) (ghat : Obs N → Lat K M) (hhat : IsDiffeoWithInv fhat ghat X) :
    ∀ (z : Lat K M) (S : Set (Fin N)), S.Nonempty →
      subRank f z S = subRank fhat (ghat (f z)) S := by
  classical
  intro z S _hS
  -- Notation for the two object-space maps and their candidate inverses
  let h : Lat K M → Lat K M := fun w => ghat (f w)
  let G : Lat K M → Lat K M := fun w => g (fhat w)

  -- Membership facts for within-set composition
  have hzX : f z ∈ X := by
    have : f z ∈ Set.range f := ⟨z, rfl⟩
    simpa [hf.2.2.1] using this
  have hzX' : fhat (h z) ∈ X := by
    have : fhat (h z) ∈ Set.range fhat := ⟨h z, rfl⟩
    simpa [hhat.2.2.1] using this

  -- Global equalities of functions (on their natural domains)
  -- 1) f̂ ∘ h = f
  have fh_eq : (fun w => fhat (h w)) = f := by
    funext w
    -- Since f w ∈ X = range f̂, write f w = f̂ y and use ĝ ∘ f̂ = id
    have hxX : f w ∈ X := by
      have : f w ∈ Set.range f := ⟨w, rfl⟩; simpa [hf.2.2.1] using this
    have hxR : f w ∈ Set.range fhat := by simpa [hhat.2.2.1] using hxX
    rcases hxR with ⟨y, hy⟩
    calc
      fhat (h w) = fhat (ghat (f w)) := rfl
      _ = fhat (ghat (fhat y)) := by simpa [hy]
      _ = fhat y := by simpa [hhat.2.2.2 y]
      _ = f w := by simpa [hy]

  -- 2) h ∘ G = id
  have hG_id : (fun w => h (G w)) = (fun w => w) := by
    funext w
    -- f (G w) = f̂ w since f̂ w ∈ X = range f
    have hxX : fhat w ∈ X := by
      have : fhat w ∈ Set.range fhat := ⟨w, rfl⟩; simpa [hhat.2.2.1] using this
    have hxR : fhat w ∈ Set.range f := by simpa [hf.2.2.1] using hxX
    rcases hxR with ⟨z0, hz0⟩
    have hg0 : g (f z0) = z0 := hf.2.2.2 z0
    calc
      h (G w) = ghat (f (G w)) := rfl
      _ = ghat (f (g (fhat w))) := rfl
      _ = ghat (f (g (f z0))) := by simpa [G, hz0]
      _ = ghat (f z0) := by simpa [hg0]
      _ = ghat (fhat w) := by simpa [hz0]
      _ = w := by simpa [hhat.2.2.2 w]

  -- 3) G ∘ h = id
  have Gh_id : (fun w => G (h w)) = (fun w => w) := by
    funext w
    have : fhat (h w) = f w := by
      -- from fh_eq (function equality)
      simpa using congrArg (fun F => F w) fh_eq
    simpa [G, h, this, hf.2.2.2]  -- g (f w) = w

  -- Differentiability witnesses (within-set where necessary)
  have h_cont_f : ContDiff ℝ 1 f := hf.1
  have h_cont_fhat : ContDiff ℝ 1 fhat := hhat.1
  have h_contWithin_ghat_at : ContDiffWithinAt ℝ 1 ghat X (f z) := (hhat.2.1.contDiffWithinAt hzX)
  have h_contWithin_g_at : ContDiffWithinAt ℝ 1 g X (fhat (h z)) := (hf.2.1.contDiffWithinAt hzX')
  have h_diffAt_f : DifferentiableAt ℝ f z := (h_cont_f.contDiffAt).differentiableAt (by decide)
  have h_diffAt_fhat_hz : DifferentiableAt ℝ fhat (h z) :=
    (h_cont_fhat.contDiffAt).differentiableAt (by decide)

  -- h is differentiable at z by within-set chain rule and range condition
  have h_event_X : ∀ᶠ x' in 𝓝 z, f x' ∈ X :=
    Filter.Eventually.of_forall (fun x' => by
      have : f x' ∈ Set.range f := ⟨x', rfl⟩; simpa [hf.2.2.1] using this)
  have h_hasWithin_ghat : HasFDerivWithinAt ghat (fderivWithin ℝ ghat X (f z)) X (f z) :=
    (h_contWithin_ghat_at.differentiableWithinAt (by decide)).hasFDerivWithinAt
  have h_hasAt_f : HasFDerivAt f (fderiv ℝ f z) z := h_diffAt_f.hasFDerivAt
  have h_hasAt_h : HasFDerivAt h (((fderivWithin ℝ ghat X (f z)) ∘L (fderiv ℝ f z))) z :=
    HasFDerivWithinAt.comp_hasFDerivAt (f:=f) (x:=z) (g:=ghat)
      (g':=fderivWithin ℝ ghat X (f z)) (t:=X) h_hasWithin_ghat h_hasAt_f h_event_X

  -- G is differentiable at h z by the same reasoning
  have h_event_X2 : ∀ᶠ y in 𝓝 (h z), fhat y ∈ X :=
    Filter.Eventually.of_forall (fun y => by
      have : fhat y ∈ Set.range fhat := ⟨y, rfl⟩; simpa [hhat.2.2.1] using this)
  have h_hasWithin_g : HasFDerivWithinAt g (fderivWithin ℝ g X (fhat (h z))) X (fhat (h z)) :=
    (h_contWithin_g_at.differentiableWithinAt (by decide)).hasFDerivWithinAt
  have h_hasAt_fhat : HasFDerivAt fhat (fderiv ℝ fhat (h z)) (h z) := h_diffAt_fhat_hz.hasFDerivAt
  have h_hasAt_G : HasFDerivAt G (((fderivWithin ℝ g X (fhat (h z))) ∘L (fderiv ℝ fhat (h z)))) (h z) :=
    HasFDerivWithinAt.comp_hasFDerivAt (f:=fhat) (x:=(h z)) (g:=g)
      (g':=fderivWithin ℝ g X (fhat (h z))) (t:=X) h_hasWithin_g h_hasAt_fhat h_event_X2

  -- Matrices and bases for chosen rows S and latent/pair spaces
  let rowEmb : S → Fin N := fun s => (s : Fin N)
  -- Define the row-submatrices
  let Jf_S : Matrix S (Fin K × Fin M) ℝ := (jac f z).submatrix rowEmb id
  let Jfhat_S : Matrix S (Fin K × Fin M) ℝ := (jac fhat (h z)).submatrix rowEmb id

  -- Identify them as matrices of composed linear maps via the Scratch bridge
  have JfS_eq_toMat :
      Jf_S
        = LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) (Pi.basisFun ℝ S)
            (LinearBridge.projS S ∘ₗ (fderiv ℝ f z).toLinearMap ∘ₗ LinearBridge.uncurryLM K M) :=
    LinearBridge.jac_submatrix_eq_toMatrix_comp K M N f z S
  have JfhS_eq_toMat :
      Jfhat_S
        = LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) (Pi.basisFun ℝ S)
            (LinearBridge.projS S ∘ₗ (fderiv ℝ fhat (h z)).toLinearMap ∘ₗ LinearBridge.uncurryLM K M) :=
    LinearBridge.jac_submatrix_eq_toMatrix_comp K M N fhat (h z) S

  -- Choose a standard basis for the latent space indexed by pairs
  -- via reindexing the dependent Pi-basis.
  let vLat :=
    (Pi.basis (fun _ : Fin K => (Pi.basisFun ℝ (Fin M)))).reindex
      (Equiv.sigmaEquivProd _ _ : (Σ _ : Fin K, Fin M) ≃ (Fin K × Fin M))

  -- Define left and right linear maps for the chain rule factorization
  let L_left  :
      (Lat K M →ₗ[ℝ] (S → ℝ)) :=
    (LinearBridge.projS S) ∘ₗ (fderiv ℝ fhat (h z)).toLinearMap
  let L_right_h :
      (LinearBridge.Pair K M →ₗ[ℝ] Lat K M) :=
    ((fderivWithin ℝ ghat X (f z)).toLinearMap)
      ∘ₗ ((fderiv ℝ f z).toLinearMap)
      ∘ₗ (LinearBridge.uncurryLM K M)
  let L_right_id :
      (LinearBridge.Pair K M →ₗ[ℝ] Lat K M) :=
    (LinearBridge.uncurryLM K M)

  -- Equality of derivatives from the global identity f = f̂ ∘ h
  have hdf_eq :
      fderiv ℝ (fhat ∘ h) z = fderiv ℝ f z := by
    -- rewrite goal to the lambda form for comp
    change fderiv ℝ (fun w => fhat (h w)) z = fderiv ℝ f z
    have : HasFDerivAt (fun w => fhat (h w)) (fderiv ℝ f z) z :=
      (Filter.EventuallyEq.of_eq (by simpa [Function.comp, fh_eq])).hasFDerivAt_iff.mpr h_hasAt_f
    simpa using this.fderiv

  -- Express Jf_S with the derivative of the composition using the bridge and hdf_eq
  have JfS_comp_toMat :
      Jf_S
        = LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) (Pi.basisFun ℝ S)
            ((LinearBridge.projS S)
              ∘ₗ (fderiv ℝ (fhat ∘ h) z).toLinearMap
              ∘ₗ LinearBridge.uncurryLM K M) := by
    classical
    -- start from the bridge for f and rewrite the middle derivative
    have JfS_eq := JfS_eq_toMat
    have hdfL := congrArg ContinuousLinearMap.toLinearMap hdf_eq
    have hcongr :
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) (Pi.basisFun ℝ S)
          (LinearBridge.projS S ∘ₗ ↑(fderiv ℝ f z) ∘ₗ LinearBridge.uncurryLM K M)
        =
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) (Pi.basisFun ℝ S)
          (LinearBridge.projS S ∘ₗ ↑(fderiv ℝ (fhat ∘ h) z) ∘ₗ LinearBridge.uncurryLM K M) := by
      simpa [LinearMap.comp_assoc] using
        congrArg
          (fun T : (Lat K M →ₗ[ℝ] (Obs N)) =>
            (LinearBridge.projS S) ∘ₗ T ∘ₗ LinearBridge.uncurryLM K M)
          hdfL.symm
    simpa [JfS_eq, hcongr]

  -- Chain rule: derivative of the composition at z
  have hdf_comp :
      fderiv ℝ (fhat ∘ h) z
        = (fderiv ℝ fhat (h z)).comp ((fderivWithin ℝ ghat X (f z)).comp (fderiv ℝ f z)) := by
    -- derivative of f̂ ∘ h at z
    simpa [Function.comp, ContinuousLinearMap.comp_assoc] using
      (HasFDerivAt.fderiv (HasFDerivAt.comp z h_hasAt_fhat h_hasAt_h))

  -- Normalize the middle derivative via the chain rule identity
  have Aeq :
      ((LinearBridge.projS S)
          ∘ₗ (fderiv ℝ (fhat ∘ h) z).toLinearMap
          ∘ₗ LinearBridge.uncurryLM K M)
        = L_left ∘ₗ L_right_h := by
    classical
    have hdfL := congrArg ContinuousLinearMap.toLinearMap hdf_comp
    -- push the equality through left/right composition
    simpa [LinearMap.comp_assoc, L_left, L_right_h]
      using
        congrArg
          (fun T : (Lat K M →ₗ[ℝ] (Obs N)) =>
            (LinearBridge.projS S) ∘ₗ T ∘ₗ LinearBridge.uncurryLM K M)
          hdfL

  -- Express Jf_S via toMatrix_comp with the latent basis vLat
  have JfS_fact :
      Jf_S
        = LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) (Pi.basisFun ℝ S)
            (L_left ∘ₗ L_right_h) := by
    classical
    simpa [JfS_comp_toMat, Aeq]
      using rfl

  have JfhS_fact :
      Jfhat_S
        = LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) (Pi.basisFun ℝ S)
            (L_left ∘ₗ L_right_id) := by
    classical
    simpa [JfhS_eq_toMat, L_left, L_right_id, LinearMap.comp_assoc]

  -- Use toMatrix_comp to factor both sides as A * B
  have JfS_prod :
      Jf_S
        = LinearMap.toMatrix vLat (Pi.basisFun ℝ S) L_left
            *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_h := by
    classical
    simpa [JfS_fact, LinearMap.toMatrix_comp] using
      (LinearMap.toMatrix_comp
        (v₁:=Pi.basisFun ℝ (Fin K × Fin M)) (v₂:=vLat) (v₃:=Pi.basisFun ℝ S)
        L_left L_right_h)

  have JfhS_prod :
      Jfhat_S
        = LinearMap.toMatrix vLat (Pi.basisFun ℝ S) L_left
            *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_id := by
    classical
    simpa [JfhS_fact, LinearMap.toMatrix_comp] using
      (LinearMap.toMatrix_comp
        (v₁:=Pi.basisFun ℝ (Fin K × Fin M)) (v₂:=vLat) (v₃:=Pi.basisFun ℝ S)
        L_left L_right_id)

  -- Matrix identity: toMatrix(uncurry) * toMatrix(curry) = 1 on Lat (basis vLat)
  have uncurry_curry_one :
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat (LinearBridge.uncurryLM K M)
        *
      LinearMap.toMatrix vLat (Pi.basisFun ℝ (Fin K × Fin M)) (LinearBridge.curryLM K M)
        = (1 : Matrix (Fin K × Fin M) (Fin K × Fin M) ℝ) := by
    classical
    -- toMatrix (uncurry ∘ curry) = toMatrix(uncurry) * toMatrix(curry) = 1 on Lat
    have h3 := LinearMap.toMatrix_comp
      (v₁:=vLat) (v₂:=Pi.basisFun ℝ (Fin K × Fin M)) (v₃:=vLat)
      (LinearBridge.uncurryLM K M) (LinearBridge.curryLM K M)
    have hIdLat :
        LinearMap.toMatrix vLat vLat
          ((LinearBridge.uncurryLM K M).comp (LinearBridge.curryLM K M)) = 1 := by
      simpa [LinearBridge.comp_uncurry_curry_id_lat K M] using
        (LinearMap.toMatrix_id (v₁:=vLat))
    -- from h3: toMatrix(comp) = toMatrix(uncurry) * toMatrix(curry)
    -- rewrite LHS to 1 via hIdLat
    simpa [hIdLat, LinearMap.toMatrix_comp] using h3.symm

  -- Build the "bridge" matrix H so that Jf_S = Jfhat_S * H
  -- H = toMatrix(curry) * toMatrix((d h) ∘ uncurry)
  let Hh :
    Matrix (Fin K × Fin M) (Fin K × Fin M) ℝ
    :=
    LinearMap.toMatrix vLat (Pi.basisFun ℝ (Fin K × Fin M)) (LinearBridge.curryLM K M)
      *
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_h

  have Jf_eq_Jfh_mul_H :
      Jf_S = Jfhat_S * Hh := by
    classical
    -- abbreviations
    set A := (LinearMap.toMatrix vLat (Pi.basisFun ℝ S) L_left)
    set B_id := (LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_id)
    set C := (LinearMap.toMatrix vLat (Pi.basisFun ℝ (Fin K × Fin M)) (LinearBridge.curryLM K M))
    set B_h := (LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_h)
    have hId : B_id * C = (1 : Matrix (Fin K × Fin M) (Fin K × Fin M) ℝ) := by
      simpa [B_id, C] using uncurry_curry_one
    -- A * B_h = (A * B_id) * (C * B_h)
    have step :
        A * B_h = (A * B_id) * (C * B_h) := by
      calc
        A * B_h = A * ((B_id * C) * B_h) := by
          simp [hId, Matrix.mul_assoc]
        _ = ((A * B_id) * C) * B_h := by
          simp [Matrix.mul_assoc]
        _ = (A * B_id) * (C * B_h) := by
          simp [Matrix.mul_assoc]
    -- Rewrite both sides to Jf_S and Jfhat_S and unfold Hh
    simpa [A, B_id, C, B_h, JfS_prod, JfhS_prod, Hh, Matrix.mul_assoc] using step

  -- By rank submultiplicativity on the left factor we get one inequality
  have hle1 : (Jf_S.rank) ≤ (Jfhat_S.rank) := by
    classical
    simpa [Jf_eq_Jfh_mul_H] using Matrix.rank_mul_le_left Jfhat_S Hh

  -- Symmetric argument with G yields the converse inequality
  -- Define maps for the other composition f̂ = f ∘ G at point h z
  let L_left' :
      (Lat K M →ₗ[ℝ] (S → ℝ)) :=
    (LinearBridge.projS S) ∘ₗ (fderiv ℝ f z).toLinearMap
  let L_right_G :
      (LinearBridge.Pair K M →ₗ[ℝ] Lat K M) :=
    ((fderivWithin ℝ g X (fhat (h z)) ∘SL fderiv ℝ fhat (h z))).toLinearMap
      ∘ₗ (LinearBridge.uncurryLM K M)

  -- Global identity: f̂ = f ∘ G, hence d f̂ (h z) = (d f z) ∘ (d G (h z))
  have fhat_eq_f_comp_G : (fun w => fhat w) = (fun w => f (G w)) := by
    funext w
    -- since fhat w ∈ X = range f
    have hxX : fhat w ∈ X := by
      have : fhat w ∈ Set.range fhat := ⟨w, rfl⟩; simpa [hhat.2.2.1] using this
    have hxR : fhat w ∈ Set.range f := by simpa [hf.2.2.1] using hxX
    rcases hxR with ⟨z0, hz0⟩
    have hg0 : g (f z0) = z0 := hf.2.2.2 z0
    have hfg : f (G w) = fhat w := by
      -- unfold and rewrite via witnesses from range facts
      calc
        f (G w) = f (g (fhat w)) := by rfl
        _ = f (g (f z0)) := by simpa [hz0]
        _ = f z0 := by simpa [hg0]
        _ = fhat w := by simpa [hz0]
    simpa [eq_comm, hfg]

  have d_fhat_eq_df_comp_dG :
      (fderiv ℝ fhat (h z))
        = (fderiv ℝ f z).comp (fderivWithin ℝ g X (fhat (h z)) ∘SL fderiv ℝ fhat (h z)) := by
    -- derivative for f ∘ G at h z, keeping the within-derivative form for G
    have Ghz : G (h z) = z := by
      simpa using congrArg (fun F => F z) Gh_id
    have hf_at_Ghz : HasFDerivAt f (fderiv ℝ f z) (G (h z)) := by
      simpa [Ghz] using h_hasAt_f
    have hcomp :
        HasFDerivAt (fun w => f (G w))
          ((fderiv ℝ f z).comp (fderivWithin ℝ g X (fhat (h z)) ∘SL fderiv ℝ fhat (h z))) (h z) :=
      HasFDerivAt.comp (h z) hf_at_Ghz h_hasAt_G
    -- transfer to fhat using pointwise equality
    have hFhat :
        HasFDerivAt fhat
          ((fderiv ℝ f z).comp (fderivWithin ℝ g X (fhat (h z)) ∘SL fderiv ℝ fhat (h z))) (h z) :=
      (Filter.EventuallyEq.of_eq (by simpa [fhat_eq_f_comp_G])).hasFDerivAt_iff.mpr hcomp
    simpa using hFhat.fderiv

  -- Normalize the middle derivative for Jfhat_S via d_fhat_eq_df_comp_dG
  have AeqG :
      ((LinearBridge.projS S)
          ∘ₗ (fderiv ℝ fhat (h z)).toLinearMap
          ∘ₗ LinearBridge.uncurryLM K M)
        = L_left' ∘ₗ L_right_G := by
    classical
    have hdfL := congrArg ContinuousLinearMap.toLinearMap d_fhat_eq_df_comp_dG
    simpa [LinearMap.comp_assoc, L_left', L_right_G]
      using
        congrArg
          (fun T : (Lat K M →ₗ[ℝ] (Obs N)) =>
            (LinearBridge.projS S) ∘ₗ T ∘ₗ LinearBridge.uncurryLM K M)
          hdfL

  have JfhS_prod' :
      Jfhat_S
        = LinearMap.toMatrix vLat (Pi.basisFun ℝ S) L_left'
            *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_G := by
    classical
    -- from the bridge and AeqG plus toMatrix_comp
    have JfhS_comp :
        Jfhat_S
          = LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) (Pi.basisFun ℝ S)
              ((LinearBridge.projS S)
                ∘ₗ (fderiv ℝ fhat (h z)).toLinearMap
                ∘ₗ LinearBridge.uncurryLM K M) :=
      JfhS_eq_toMat
    have :
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) (Pi.basisFun ℝ S)
            ((LinearBridge.projS S)
              ∘ₗ (fderiv ℝ fhat (h z)).toLinearMap
              ∘ₗ LinearBridge.uncurryLM K M)
      =
        LinearMap.toMatrix vLat (Pi.basisFun ℝ S) L_left'
          *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_G := by
      -- rewrite middle via AeqG then apply toMatrix_comp
      have := LinearMap.toMatrix_comp
        (v₁:=Pi.basisFun ℝ (Fin K × Fin M)) (v₂:=vLat) (v₃:=Pi.basisFun ℝ S)
        L_left' L_right_G
      simpa [AeqG]
        using this
    simpa [JfhS_comp] using this

  -- Also express Jf_S with `L_left'` and `L_right_id`
  have JfS_prod_alt :
      Jf_S
        = LinearMap.toMatrix vLat (Pi.basisFun ℝ S) L_left'
            *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_id := by
    classical
    simpa [JfS_eq_toMat, L_left', L_right_id, LinearMap.toMatrix_comp, LinearMap.comp_assoc]
      using (LinearMap.toMatrix_comp
        (v₁:=Pi.basisFun ℝ (Fin K × Fin M)) (v₂:=vLat) (v₃:=Pi.basisFun ℝ S)
        L_left' L_right_id)

  let HG :
    Matrix (Fin K × Fin M) (Fin K × Fin M) ℝ
    :=
    LinearMap.toMatrix vLat (Pi.basisFun ℝ (Fin K × Fin M)) (LinearBridge.curryLM K M)
      *
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_G

  have Jfh_eq_Jf_mul_HG :
      Jfhat_S = Jf_S * HG := by
    classical
    -- abbreviations
    set A := (LinearMap.toMatrix vLat (Pi.basisFun ℝ S) L_left') with hA
    set B_id := (LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_id) with hBid
    set C := (LinearMap.toMatrix vLat (Pi.basisFun ℝ (Fin K × Fin M)) (LinearBridge.curryLM K M)) with hC
    set B_G := (LinearMap.toMatrix (Pi.basisFun ℝ (Fin K × Fin M)) vLat L_right_G) with hBG
    have hId : B_id * C = (1 : Matrix (Fin K × Fin M) (Fin K × Fin M) ℝ) := by
      simpa [hBid, hC] using uncurry_curry_one
    -- proof via chained equalities
    have eq0 : Jfhat_S = A * B_G := by
      simpa [hA, hBG] using JfhS_prod'
    have hIDstep : B_id * (C * B_G) = B_G := by
      calc
        B_id * (C * B_G)
            = (B_id * C) * B_G := by simp [Matrix.mul_assoc]
        _ = (1 : Matrix (Fin K × Fin M) (Fin K × Fin M) ℝ) * B_G := by simpa [hId]
        _ = B_G := by simp
    have eq1 : A * B_G = A * (B_id * (C * B_G)) := by
      simpa [hIDstep]
    have eq2 : A * (B_id * (C * B_G)) = ((A * B_id) * C) * B_G := by
      -- A * (B * (C * D)) = ((A*B) * C) * D
      simp [Matrix.mul_assoc]
    have eq3 : ((A * B_id) * C) * B_G = (A * B_id) * (C * B_G) := by
      simp [Matrix.mul_assoc]
    have eq4 : Jfhat_S = (A * B_id) * (C * B_G) := by
      exact (eq0.trans eq1).trans eq2 |> fun h => h.trans eq3
    -- conclude
    simpa [hA, hBid, hC, hBG, JfS_prod_alt, HG, Matrix.mul_assoc] using eq4

  have hle2 : (Jfhat_S.rank) ≤ (Jf_S.rank) := by
    classical
    simpa [Jfh_eq_Jf_mul_HG] using Matrix.rank_mul_le_left Jf_S HG

  -- Conclude equality of subranks
  have hrank_eq : Jf_S.rank = Jfhat_S.rank := le_antisymm hle1 hle2
  simpa [subRank, Jf_S, Jfhat_S] using hrank_eq
