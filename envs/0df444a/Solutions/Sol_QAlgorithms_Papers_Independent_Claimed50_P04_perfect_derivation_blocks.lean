-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P04.perfect_derivation_blocks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:02:11.334649+00:00
-- url     : https://prove2.me/submissions/5bca6190-faa1-4673-9c0e-05517033d57a

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P04
open QAlgorithms.Papers.Independent.Claimed50.P04
noncomputable section

open Set

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Frontier30.P26
  (Invariant LieAdmissible ClosedCone CompactlyEmbedded CompactCartan Hermitian bracketSpan
    TubeType)

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedSpace

section FurtherStructure

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

theorem g58c_csymm (P : SpindlerPresentation (G := G))
    (t : P.V × (LieAlgebra.center ℝ G) × P.L) :
    (P.coordinates.symm t : G) = (t.1 : G) + (t.2.1 : G) + (t.2.2 : G) := by
  have h := P.reconstruct (P.coordinates.symm t)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem g58c_cof (P : SpindlerPresentation (G := G)) (v : P.V) (z : LieAlgebra.center ℝ G) (l : P.L) :
    P.coordinates ((v : G) + (z : G) + (l : G)) = (v, z, l) := by
  rw [← g58c_csymm P (v, z, l), LinearEquiv.apply_symm_apply]

theorem g58c_cV (P : SpindlerPresentation (G := G)) (v : P.V) :
    P.coordinates (v : G) = (v, 0, 0) := by
  have := g58c_cof P v 0 0; simpa using this

theorem g58c_cZ (P : SpindlerPresentation (G := G)) (z : LieAlgebra.center ℝ G) :
    P.coordinates (z : G) = (0, z, 0) := by
  have := g58c_cof P 0 z 0; simpa using this

theorem g58c_cL (P : SpindlerPresentation (G := G)) (l : P.L) :
    P.coordinates (l : G) = (0, 0, l) := by
  have := g58c_cof P 0 0 l; simpa using this

theorem g58c_central (z : LieAlgebra.center ℝ G) (y : G) : ⁅(z : G), y⁆ = 0 := by
  have h := (LieModule.mem_maxTrivSubmodule ℝ G G (z : G)).1 z.2 y
  rw [← lie_skew, h, neg_zero]

theorem g58c_central' (z : LieAlgebra.center ℝ G) (y : G) : ⁅y, (z : G)⁆ = 0 :=
  (LieModule.mem_maxTrivSubmodule ℝ G G (z : G)).1 z.2 y

/-- bracket in coordinates -/
theorem g58c_br (P : SpindlerPresentation (G := G)) (a b : G) :
    ⁅a, b⁆ = ((spindlerAction P (P.coordinates a).2.2 (P.coordinates b).1 -
        spindlerAction P (P.coordinates b).2.2 (P.coordinates a).1 : P.V) : G) +
      ((spindlerBracket P (P.coordinates a).1 (P.coordinates b).1 : LieAlgebra.center ℝ G) : G) +
      ((⁅(P.coordinates a).2.2, (P.coordinates b).2.2⁆ : P.L) : G) := by
  conv_lhs => rw [← P.reconstruct a, ← P.reconstruct b]
  simp only [lie_add, add_lie, g58c_central, g58c_central', add_zero, zero_add,
    Submodule.coe_sub, spindlerAction, spindlerBracket, LinearMap.coe_mk, AddHom.coe_mk,
    LieSubalgebra.coe_bracket]
  rw [← lie_skew ((P.coordinates a).1 : G) ((P.coordinates b).2.2 : G)]
  abel

theorem g58c_cbr (P : SpindlerPresentation (G := G)) (a b : G) :
    P.coordinates ⁅a, b⁆ = (spindlerAction P (P.coordinates a).2.2 (P.coordinates b).1 -
        spindlerAction P (P.coordinates b).2.2 (P.coordinates a).1,
      spindlerBracket P (P.coordinates a).1 (P.coordinates b).1,
      ⁅(P.coordinates a).2.2, (P.coordinates b).2.2⁆) := by
  rw [g58c_br P a b, g58c_cof]

theorem g58c_act0 (P : SpindlerPresentation (G := G)) (v : P.V) : spindlerAction P 0 v = 0 := by
  ext; simp [spindlerAction]

theorem g58c_actz (P : SpindlerPresentation (G := G)) (x : P.L) : spindlerAction P x 0 = 0 := by
  ext; simp [spindlerAction]

theorem g58c_bskew (P : SpindlerPresentation (G := G)) (v w : P.V) :
    spindlerBracket P w v = - spindlerBracket P v w := by
  ext; simp [spindlerBracket]

theorem g58c_b0 (P : SpindlerPresentation (G := G)) (v : P.V) :
    spindlerBracket P v 0 = 0 ∧ spindlerBracket P 0 v = 0 := by
  constructor <;> (ext; simp [spindlerBracket])

theorem g58c_Dz (D : LieDerivation ℝ G G) (z : LieAlgebra.center ℝ G) :
    D (z : G) ∈ LieAlgebra.center ℝ G := by
  rw [LieModule.mem_maxTrivSubmodule]
  intro y
  have h := D.apply_lie_eq_sub y z
  rw [g58c_central' z y, map_zero, g58c_central z] at h
  rw [sub_zero] at h; exact h.symm

theorem g58c_cDz (P : SpindlerPresentation (G := G)) (D : LieDerivation ℝ G G)
    (z : LieAlgebra.center ℝ G) :
    P.coordinates (D (z : G)) = (0, ⟨D z, g58c_Dz D z⟩, 0) := by
  have := g58c_cZ P ⟨D z, g58c_Dz D z⟩
  simpa using this

theorem g58c_be (P : SpindlerPresentation (G := G)) (DV : Module.End ℝ P.V)
    (DZ : Module.End ℝ (LieAlgebra.center ℝ G)) (g : G) :
    blockEnd P DV DZ g = (DV (P.coordinates g).1 : G) + (DZ (P.coordinates g).2.1 : G) := by
  simp only [blockEnd, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [g58c_csymm]
  simp

theorem g58c_span (P : SpindlerPresentation (G := G))
    (hp : LieAlgebra.derivedSeries ℝ G 1 = ⊤) (v : P.V) :
    v ∈ Submodule.span ℝ (Set.range (fun q : P.L × P.V => spindlerAction P q.1 q.2)) := by
  set S := Submodule.span ℝ (Set.range (fun q : P.L × P.V => spindlerAction P q.1 q.2))
  have hmem : (v : G) ∈ LieAlgebra.derivedSeries ℝ G 1 := by rw [hp]; trivial
  rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero] at hmem
  rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span] at hmem
  let f : G →ₗ[ℝ] P.V := (LinearMap.fst ℝ _ _).comp P.coordinates.toLinearMap
  have hle : Submodule.span ℝ {m | ∃ (x : (⊤ : LieIdeal ℝ G)) (n : (⊤ : LieIdeal ℝ G)),
      ⁅(x : G), (n : G)⁆ = m} ≤ S.comap f := by
    rw [Submodule.span_le]
    rintro m ⟨x, n, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, f, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearMap.fst_apply]
    rw [g58c_cbr]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨(_, _), rfl⟩)
      (Submodule.subset_span ⟨(_, _), rfl⟩)
  have := hle hmem
  simpa [f, g58c_cV] using this

theorem g58c_fwd (P : SpindlerPresentation (G := G)) (hp : LieAlgebra.derivedSeries ℝ G 1 = ⊤)
    (D : LieDerivation ℝ G G) (hD : ∀ x : P.L, D (x : G) = 0) :
    ∃ DV : Module.End ℝ P.V, ∃ DZ : Module.End ℝ (LieAlgebra.center ℝ G),
        D.toLinearMap = blockEnd P DV DZ ∧
        (∀ x : P.L, ∀ v : P.V, DV (spindlerAction P x v) = spindlerAction P x (DV v)) ∧
        (∀ v w : P.V, DZ (spindlerBracket P v w) =
          spindlerBracket P (DV v) w + spindlerBracket P v (DV w)) := by
  have hL := P.reductive
  let cD : P.V →ₗ[ℝ] P.V × (LieAlgebra.center ℝ G) × P.L :=
    P.coordinates.toLinearMap.comp (D.toLinearMap.comp P.V.subtype)
  let α : Module.End ℝ P.V := (LinearMap.fst ℝ _ _).comp cD
  let ζ : P.V →ₗ[ℝ] LieAlgebra.center ℝ G :=
    (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp cD)
  let φ : P.V →ₗ[ℝ] P.L := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp cD)
  have hα : ∀ v, α v = (P.coordinates (D (v : G))).1 := fun v => rfl
  have hζ : ∀ v, ζ v = (P.coordinates (D (v : G))).2.1 := fun v => rfl
  have hφ : ∀ v, φ v = (P.coordinates (D (v : G))).2.2 := fun v => rfl
  have hx : ∀ (x : P.L) (v : P.V), P.coordinates (D (spindlerAction P x v : G)) =
      (spindlerAction P x (α v), 0, ⁅x, φ v⁆) := by
    intro x v
    have e : ((spindlerAction P x v : P.V) : G) = ⁅(x : G), (v : G)⁆ := rfl
    rw [e, D.apply_lie_eq_sub, hD x, lie_zero, sub_zero, g58c_cbr, g58c_cL]
    simp only [g58c_act0, g58c_actz, sub_zero, (g58c_b0 P _).2, hα, hφ]
  have hs : ∀ v w : P.V, spindlerAction P (φ v) w = spindlerAction P (φ w) v := by
    intro v w
    have h1 := congrArg (fun t => t.1) (congrArg P.coordinates (D.apply_lie_eq_sub (v : G) (w : G)))
    have e : ⁅(v : G), (w : G)⁆ = ((⟨_, P.vv_central v w⟩ : LieAlgebra.center ℝ G) : G) := rfl
    try simp only at h1
    rw [e, g58c_cDz, map_sub, g58c_cbr, g58c_cbr, g58c_cV, g58c_cV] at h1
    simp only [Prod.fst_sub, g58c_act0, zero_sub, ← hφ] at h1
    have h2 : spindlerAction P (φ v) w - spindlerAction P (φ w) v = 0 := by
      rw [h1]; abel
    exact sub_eq_zero.1 h2
  have hφx : ∀ (x : P.L) (v : P.V), φ (spindlerAction P x v) = ⁅x, φ v⁆ := by
    intro x v; rw [hφ, hx]
  have hζx : ∀ (x : P.L) (v : P.V), ζ (spindlerAction P x v) = 0 := by
    intro x v; rw [hζ, hx]
  have hαx : ∀ (x : P.L) (v : P.V), α (spindlerAction P x v) = spindlerAction P x (α v) := by
    intro x v; rw [hα, hx]
  have hcomm : ∀ v w : P.V, ⁅φ v, φ w⁆ = 0 := by
    intro v w
    have h1 := hφx (φ v) w
    have h2 := hφx (φ w) v
    rw [hs v w, h2, ← lie_skew] at h1
    rw [neg_eq_iff_add_eq_zero] at h1
    have : (2 : ℝ) • ⁅φ v, φ w⁆ = 0 := by rw [two_smul]; exact h1
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  let I : LieIdeal ℝ P.L :=
    { toSubmodule := LinearMap.range φ
      lie_mem := by
        rintro x m ⟨v, rfl⟩
        exact ⟨spindlerAction P x v, hφx x v⟩ }
  have hab : IsLieAbelian I := by
    constructor
    rintro ⟨a, v, rfl⟩ ⟨b, w, rfl⟩
    apply Subtype.ext
    show ⁅φ v, φ w⁆ = 0
    exact hcomm v w
  have hIrad : I ≤ LieAlgebra.radical ℝ P.L :=
    (LieAlgebra.LieIdeal.solvable_iff_le_radical ℝ P.L I).1 inferInstance
  rw [LieAlgebra.HasCentralRadical.radical_eq_center] at hIrad
  have hφc : ∀ (x : P.L) (v : P.V), φ (spindlerAction P x v) = 0 := by
    intro x v
    rw [hφx]
    have hm : φ v ∈ LieAlgebra.center ℝ P.L := hIrad ⟨v, rfl⟩
    exact (LieModule.mem_maxTrivSubmodule ℝ P.L P.L (φ v)).1 hm x
  have hφ0 : ∀ v, φ v = 0 := by
    intro v
    have hv := g58c_span P hp v
    have hle : Submodule.span ℝ (Set.range (fun q : P.L × P.V => spindlerAction P q.1 q.2)) ≤
        LinearMap.ker φ := by
      rw [Submodule.span_le]; rintro _ ⟨q, rfl⟩; exact hφc q.1 q.2
    exact hle hv
  have hζ0 : ∀ v, ζ v = 0 := by
    intro v
    have hv := g58c_span P hp v
    have hle : Submodule.span ℝ (Set.range (fun q : P.L × P.V => spindlerAction P q.1 q.2)) ≤
        LinearMap.ker ζ := by
      rw [Submodule.span_le]; rintro _ ⟨q, rfl⟩; exact hζx q.1 q.2
    exact hle hv
  let DZ : Module.End ℝ (LieAlgebra.center ℝ G) :=
    (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
      (P.coordinates.toLinearMap.comp (D.toLinearMap.comp (LieAlgebra.center ℝ G).toSubmodule.subtype)))
  have hDZ : ∀ z : LieAlgebra.center ℝ G, ((DZ z : LieAlgebra.center ℝ G) : G) = D (z : G) := by
    intro z
    show (((P.coordinates (D (z : G))).2.1 : LieAlgebra.center ℝ G) : G) = _
    rw [g58c_cDz]
  have hDv : ∀ v : P.V, D (v : G) = (α v : G) := by
    intro v
    rw [← P.reconstruct (D (v : G)), ← hα, ← hζ, ← hφ, hζ0, hφ0]; simp
  refine ⟨α, DZ, ?_, hαx, ?_⟩
  · ext g
    rw [g58c_be]
    show D g = _
    conv_lhs => rw [← P.reconstruct g]
    simp only [map_add, hD, add_zero, hDv, hDZ]
  · intro v w
    apply Subtype.ext
    rw [hDZ]
    have e : ((spindlerBracket P v w : LieAlgebra.center ℝ G) : G) = ⁅(v : G), (w : G)⁆ := rfl
    rw [e, D.apply_lie_eq_sub, hDv, hDv]
    show ⁅(v : G), (α w : G)⁆ - ⁅(w : G), (α v : G)⁆ = ⁅(α v : G), (w : G)⁆ + ⁅(v : G), (α w : G)⁆
    rw [← lie_skew (α v : G) (w : G)]
    abel

theorem g58c_bwd (P : SpindlerPresentation (G := G)) (DV : Module.End ℝ P.V)
    (DZ : Module.End ℝ (LieAlgebra.center ℝ G))
    (hx : ∀ x : P.L, ∀ v : P.V, DV (spindlerAction P x v) = spindlerAction P x (DV v))
    (hc : ∀ v w : P.V, DZ (spindlerBracket P v w) =
      spindlerBracket P (DV v) w + spindlerBracket P v (DV w)) :
    ∃ D : LieDerivation ℝ G G, D.toLinearMap = blockEnd P DV DZ ∧ ∀ x : P.L, D (x : G) = 0 := by
  refine ⟨{ toLinearMap := blockEnd P DV DZ, leibniz' := ?_ }, rfl, ?_⟩
  · intro a b
    rw [g58c_be, g58c_be, g58c_be, g58c_cbr]
    simp only [lie_add, g58c_central', add_zero]
    rw [g58c_br P a (DV _ : G), g58c_br P b (DV _ : G), g58c_cV, g58c_cV]
    simp only [g58c_act0, sub_zero, lie_zero, map_sub, hx, hc]
    rw [g58c_bskew P (DV (P.coordinates a).1) (P.coordinates b).1]
    simp only [Submodule.coe_sub, Submodule.coe_add, LieSubmodule.coe_add, LieSubmodule.coe_neg,
      ZeroMemClass.coe_zero, add_zero]
    abel
  · intro x
    show blockEnd P DV DZ (x : G) = 0
    rw [g58c_be, g58c_cL]; simp

/-- Lemma 3.13, PDF p. 20. Perfectness is explicit, and the converse constructs a
Lie derivation with precisely the displayed diagonal-block linear map. -/
theorem solution (ha : LieAdmissible (G := G))
    (P : SpindlerPresentation (G := G))
    (hp : LieAlgebra.derivedSeries ℝ G 1 = ⊤) :
    (∀ D : LieDerivation ℝ G G, (∀ x : P.L, D (x : G) = 0) →
      ∃ DV : Module.End ℝ P.V, ∃ DZ : Module.End ℝ (LieAlgebra.center ℝ G),
        D.toLinearMap = blockEnd P DV DZ ∧
        (∀ x : P.L, ∀ v : P.V, DV (spindlerAction P x v) = spindlerAction P x (DV v)) ∧
        (∀ v w : P.V, DZ (spindlerBracket P v w) = spindlerBracket P (DV v) w + spindlerBracket P v (DV w))) ∧
    (∀ DV : Module.End ℝ P.V, ∀ DZ : Module.End ℝ (LieAlgebra.center ℝ G),
      (∀ x : P.L, ∀ v : P.V, DV (spindlerAction P x v) = spindlerAction P x (DV v)) →
      (∀ v w : P.V, DZ (spindlerBracket P v w) = spindlerBracket P (DV v) w + spindlerBracket P v (DV w)) →
      ∃ D : LieDerivation ℝ G G, D.toLinearMap = blockEnd P DV DZ ∧
        ∀ x : P.L, D (x : G) = 0) := by
  exact ⟨fun D hD => g58c_fwd P hp D hD, fun DV DZ hx hc => g58c_bwd P DV DZ hx hc⟩

end FurtherStructure

end

