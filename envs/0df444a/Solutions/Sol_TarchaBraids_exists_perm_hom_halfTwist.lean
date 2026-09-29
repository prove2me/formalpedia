-- Prove2me | solution 1 for TarchaBraids.exists_perm_hom_halfTwist
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T19:25:46.486796+00:00
-- url     : https://prove2.me/submissions/cb92f4f0-8635-4c34-b99b-bf47881d7ead

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

namespace PermHomSol

/-- Relabelling action of the symmetric group on ordered configurations. -/
instance permAction (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (OrderedConfig n) where
  smul g p := ⟨p.1 ∘ ⇑g⁻¹, p.2.comp (g⁻¹).injective⟩
  one_smul p := by apply Subtype.ext; funext i; rfl
  mul_smul g h p := by
    apply Subtype.ext
    funext i
    show p.1 ((g * h)⁻¹ i) = p.1 (h⁻¹ (g⁻¹ i))
    rw [mul_inv_rev]
    rfl

variable {n : ℕ}

lemma smul_val (g : Equiv.Perm (Fin n)) (p : OrderedConfig n) :
    (g • p).1 = p.1 ∘ ⇑g⁻¹ := rfl

instance : ContinuousConstSMul (Equiv.Perm (Fin n)) (OrderedConfig n) where
  continuous_const_smul g := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => (continuous_apply (g⁻¹ i)).comp continuous_subtype_val

lemma proj_eq_iff (p q : OrderedConfig n) :
    configProj n p = configProj n q ↔ p ∈ MulAction.orbit (Equiv.Perm (Fin n)) q := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    refine ⟨g, ?_⟩
    apply Subtype.ext
    rw [smul_val, hg]
    funext i
    simp
  · rintro ⟨g, rfl⟩
    apply Quotient.sound
    refine ⟨g, ?_⟩
    funext i
    simp [smul_val]

/-- The action is free: a permutation fixing an injective tuple is the identity. -/
lemma smul_eq_self (p : OrderedConfig n) (g : Equiv.Perm (Fin n)) (h : g • p = p) : g = 1 := by
  have h1 : ∀ i, p.1 (g⁻¹ i) = p.1 i := fun i => congrFun (congrArg Subtype.val h) i
  have h2 : ∀ i, g⁻¹ i = i := fun i => p.2 (h1 i)
  have : g⁻¹ = 1 := Equiv.ext h2
  simpa using congrArg (·⁻¹) this

/-- Around any ordered configuration there is a neighbourhood whose translates by
nontrivial permutations miss it. -/
lemma disjoint_nbhd (e : OrderedConfig n) :
    ∃ U ∈ nhds e, ∀ g : Equiv.Perm (Fin n),
      (((g • ·) '' U) ∩ U).Nonempty → g = 1 := by
  classical
  have hsep : ∀ g : Equiv.Perm (Fin n), ∃ V W : Set (OrderedConfig n),
      IsOpen V ∧ IsOpen W ∧ e ∈ V ∧ g • e ∈ W ∧ (g ≠ 1 → Disjoint V W) := by
    intro g
    by_cases hg : g = 1
    · exact ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ, Set.mem_univ _, Set.mem_univ _,
        fun h => absurd hg h⟩
    · have hne : g • e ≠ e := fun h => hg (smul_eq_self e g h)
      obtain ⟨W', V', hW', hV', hgW', heV', hd⟩ := t2_separation hne
      exact ⟨V', W', hV', hW', heV', hgW', fun _ => hd.symm⟩
  choose V W hV hW heV hgW hdisj using hsep
  refine ⟨⋂ g : Equiv.Perm (Fin n), (V g ∩ ((g • ·) ⁻¹' (W g))), ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ ?_
    · exact isOpen_iInter_of_finite fun g =>
        (hV g).inter ((hW g).preimage (continuous_const_smul g))
    · exact Set.mem_iInter.mpr fun g => ⟨heV g, hgW g⟩
  · rintro g ⟨y, ⟨u, huU, rfl⟩, hguU⟩
    by_contra hne
    have h1 := Set.mem_iInter.mp huU g
    have h2 := Set.mem_iInter.mp hguU g
    exact Set.disjoint_left.mp (hdisj g hne) h2.1 h1.2

theorem configProj_isQuotientCovering (n : ℕ) :
    IsQuotientCoveringMap (⇑(configProj n)) (Equiv.Perm (Fin n)) where
  toIsQuotientMap := isQuotientMap_quotient_mk'
  toContinuousConstSMul := inferInstance
  apply_eq_iff_mem_orbit := proj_eq_iff _ _
  disjoint := disjoint_nbhd

theorem configProj_isCoveringMap (n : ℕ) : IsCoveringMap (configProj n) :=
  (configProj_isQuotientCovering n).isCoveringMap

section Monodromy

variable (n : ℕ)

lemma proj_smul (g : Equiv.Perm (Fin n)) (e : OrderedConfig n) :
    configProj n (g • e) = configProj n e :=
  (proj_eq_iff _ _).mpr ⟨g, rfl⟩

/-- Lifting is equivariant for the deck action. -/
lemma smul_liftPath (g : Equiv.Perm (Fin n)) (γ : C(unitInterval, UnorderedConfig n))
    (e : OrderedConfig n) (h : γ 0 = configProj n e) :
    (fun x => g • x) ∘ (configProj_isCoveringMap n).liftPath γ e h =
      (configProj_isCoveringMap n).liftPath γ (g • e) (by rw [h, proj_smul]) := by
  refine ((configProj_isCoveringMap n).eq_liftPath_iff _).mpr ⟨?_, ?_, ?_⟩
  · exact (continuous_const_smul g).comp
      ((configProj_isCoveringMap n).liftPath γ e h).continuous
  · funext t
    show configProj n (g • ((configProj_isCoveringMap n).liftPath γ e h t)) = γ t
    rw [proj_smul]
    exact congrFun ((configProj_isCoveringMap n).liftPath_lifts γ e h) t
  · show g • ((configProj_isCoveringMap n).liftPath γ e h 0) = g • e
    rw [(configProj_isCoveringMap n).liftPath_zero]

lemma smul_base_injective {g g' : Equiv.Perm (Fin n)}
    (h : g • baseOrdered n = g' • baseOrdered n) : g = g' := by
  have h1 : (g'⁻¹ * g) • baseOrdered n = baseOrdered n := by
    rw [mul_smul, h, inv_smul_smul]
  have h2 := smul_eq_self _ _ h1
  have h3 := congrArg (fun x => g' * x) h2
  simpa using h3

/-- The fibre of the covering over the base point. -/
abbrev Fib (n : ℕ) := (⇑(configProj n)) ⁻¹' {baseUnordered n}

/-- The base configuration, as a point of the fibre. -/
def basePt (n : ℕ) : Fib n := ⟨baseOrdered n, rfl⟩

/-- Deck transformations commute with monodromy. -/
lemma monodromy_deck (γq : Path.Homotopic.Quotient (baseUnordered n) (baseUnordered n))
    (g : Equiv.Perm (Fin n)) (e : Fib n)
    (hge : g • e.1 ∈ ⇑(configProj n) ⁻¹' {baseUnordered n}) :
    (((configProj_isCoveringMap n).monodromy γq ⟨g • e.1, hge⟩ : Fib n) : OrderedConfig n)
      = g • (((configProj_isCoveringMap n).monodromy γq e : Fib n) : OrderedConfig n) := by
  induction γq using Quotient.ind with
  | _ γ =>
    show (configProj_isCoveringMap n).liftPath γ.toContinuousMap (g • e.1) _ 1
      = g • ((configProj_isCoveringMap n).liftPath γ.toContinuousMap e.1 _ 1)
    rw [← smul_liftPath n g γ.toContinuousMap e.1 (by simpa using e.2.symm)]
    rfl

lemma exists_phi (γ : GeomBraidGroup n) :
    ∃ g : Equiv.Perm (Fin n), g • baseOrdered n =
      (((configProj_isCoveringMap n).monodromy γ (basePt n) : Fib n) : OrderedConfig n) :=
  (proj_eq_iff _ _).mp ((configProj_isCoveringMap n).monodromy γ (basePt n)).2

/-- The strand permutation attached to a braid (an anti-homomorphism). -/
noncomputable def phi (γ : GeomBraidGroup n) : Equiv.Perm (Fin n) := (exists_phi n γ).choose

lemma phi_spec (γ : GeomBraidGroup n) :
    (phi n γ) • baseOrdered n =
      (((configProj_isCoveringMap n).monodromy γ (basePt n) : Fib n) : OrderedConfig n) :=
  (exists_phi n γ).choose_spec

lemma phi_eq {γ : GeomBraidGroup n} {g : Equiv.Perm (Fin n)}
    (h : g • baseOrdered n =
      (((configProj_isCoveringMap n).monodromy γ (basePt n) : Fib n) : OrderedConfig n)) :
    phi n γ = g :=
  smul_base_injective n ((phi_spec n γ).trans h.symm)

lemma phi_one : phi n 1 = 1 := by
  letI := (configProj_isCoveringMap n).fundamentalGroupMulAction (baseUnordered n)
  refine phi_eq n ?_
  have h : ((1 : GeomBraidGroup n) • (basePt n) : Fib n) = basePt n := one_smul _ _
  rw [show ((configProj_isCoveringMap n).monodromy (1 : GeomBraidGroup n) (basePt n) : Fib n)
      = basePt n from h]
  show (1 : Equiv.Perm (Fin n)) • baseOrdered n = baseOrdered n
  exact one_smul _ _

lemma phi_mul (a b : GeomBraidGroup n) : phi n (a * b) = phi n b * phi n a := by
  letI := (configProj_isCoveringMap n).fundamentalGroupMulAction (baseUnordered n)
  refine phi_eq n ?_
  have hb : (((configProj_isCoveringMap n).monodromy b (basePt n) : Fib n) : OrderedConfig n)
      = (phi n b) • ((basePt n : Fib n) : OrderedConfig n) := (phi_spec n b).symm
  have hmul : ((configProj_isCoveringMap n).monodromy (a * b) (basePt n) : Fib n)
      = (configProj_isCoveringMap n).monodromy a
          ((configProj_isCoveringMap n).monodromy b (basePt n)) := mul_smul a b (basePt n)
  rw [hmul, mul_smul, phi_spec n a]
  rw [show ((configProj_isCoveringMap n).monodromy b (basePt n) : Fib n)
      = ⟨(phi n b) • ((basePt n : Fib n) : OrderedConfig n), hb ▸
          ((configProj_isCoveringMap n).monodromy b (basePt n)).2⟩ from Subtype.ext hb]
  exact (monodromy_deck n a (phi n b) (basePt n) _).symm

/-- The underlying-permutation homomorphism of the braid group. -/
noncomputable def nu (n : ℕ) : GeomBraidGroup n →* Equiv.Perm (Fin n) where
  toFun γ := (phi n γ)⁻¹
  map_one' := by rw [phi_one]; exact inv_one
  map_mul' a b := by rw [phi_mul]; exact mul_inv_rev _ _

/-- The explicit lift of the half-twist loop is the half-twist configuration itself. -/
lemma liftPath_halfTwistLoop (i : Fin (n - 1)) :
    (configProj_isCoveringMap n).liftPath (halfTwistLoop n i).toContinuousMap
      (baseOrdered n) (halfTwistLoop n i).source 1 = halfTwistConfig n i 1 := by
  have hlift : (fun t : unitInterval => halfTwistConfig n i (t : ℝ)) =
      (configProj_isCoveringMap n).liftPath (halfTwistLoop n i).toContinuousMap
        (baseOrdered n) (halfTwistLoop n i).source := by
    refine ((configProj_isCoveringMap n).eq_liftPath_iff _).mpr ⟨?_, ?_, ?_⟩
    · exact (continuous_halfTwistConfig n i).comp continuous_subtype_val
    · rfl
    · show halfTwistConfig n i ((0 : unitInterval) : ℝ) = baseOrdered n
      simpa using halfTwistConfig_zero n i
  rw [← hlift]
  show halfTwistConfig n i ((1 : unitInterval) : ℝ) = halfTwistConfig n i 1
  norm_num

lemma phi_halfTwist (i : Fin (n - 1)) :
    phi n (halfTwistBraid n i) = Equiv.swap (strandIdx i) (strandIdxSucc i) := by
  refine phi_eq n ?_
  show (Equiv.swap (strandIdx i) (strandIdxSucc i)) • baseOrdered n
    = ((configProj_isCoveringMap n).liftPath (halfTwistLoop n i).toContinuousMap
        (baseOrdered n) (halfTwistLoop n i).source 1)
  rw [liftPath_halfTwistLoop]
  apply Subtype.ext
  rw [smul_val]
  show (baseOrdered n).1 ∘ ⇑(Equiv.swap (strandIdx i) (strandIdxSucc i))⁻¹ =
    (halfTwistConfig n i 1).1
  rw [Equiv.swap_inv, halfTwistConfig_one n i]
  funext k
  simp

lemma nu_halfTwist (i : Fin (n - 1)) :
    nu n (halfTwistBraid n i) = Equiv.swap (strandIdx i) (strandIdxSucc i) := by
  show (phi n (halfTwistBraid n i))⁻¹ = _
  rw [phi_halfTwist, Equiv.swap_inv]

lemma mem_range_of_lift_loop (c : Path (baseUnordered n) (baseUnordered n))
    (hend : (configProj_isCoveringMap n).liftPath c.toContinuousMap (baseOrdered n) c.source 1
      = baseOrdered n) :
    ∃ δ : PureBraidGroup n,
      FundamentalGroup.map (configProj n) (baseOrdered n) δ
        = FundamentalGroup.fromPath ⟦c⟧ := by
  set Γ := (configProj_isCoveringMap n).liftPath c.toContinuousMap (baseOrdered n) c.source with hΓ
  set P : Path (baseOrdered n) (baseOrdered n) :=
    ⟨Γ, (configProj_isCoveringMap n).liftPath_zero _ _ _, hend⟩ with hP
  refine ⟨FundamentalGroup.fromPath ⟦P⟧, ?_⟩
  have hpath : P.map (configProj n).continuous = c := by
    ext t
    exact congrFun ((configProj_isCoveringMap n).liftPath_lifts
      c.toContinuousMap (baseOrdered n) c.source) t
  show FundamentalGroup.fromPath ⟦P.map (configProj n).continuous⟧
    = FundamentalGroup.fromPath ⟦c⟧
  rw [hpath]
  rfl

lemma nu_ker : (nu n).ker = (FundamentalGroup.map (configProj n) (baseOrdered n)).range := by
  ext γ
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro h
    have hphi : phi n γ = 1 := by
      have h1 : (phi n γ)⁻¹ = 1 := h
      simpa using congrArg (fun x : Equiv.Perm (Fin n) => x⁻¹) h1
    have hmono : (((configProj_isCoveringMap n).monodromy γ (basePt n) : Fib n)
        : OrderedConfig n) = baseOrdered n := by
      rw [← phi_spec n γ, hphi, one_smul]
    obtain ⟨c, hc⟩ := Quotient.exists_rep (FundamentalGroup.toPath γ)
    have hend : (configProj_isCoveringMap n).liftPath c.toContinuousMap
        (baseOrdered n) c.source 1 = baseOrdered n := by
      have h2 : (((configProj_isCoveringMap n).monodromy
            (⟦c⟧ : Path.Homotopic.Quotient (baseUnordered n) (baseUnordered n))
            (basePt n) : Fib n) : OrderedConfig n)
          = (configProj_isCoveringMap n).liftPath c.toContinuousMap
              (baseOrdered n) c.source 1 := rfl
      rw [← h2, hc]
      exact hmono
    obtain ⟨δ, hδ⟩ := mem_range_of_lift_loop n c hend
    refine ⟨δ, ?_⟩
    rw [hδ]
    show FundamentalGroup.fromPath ⟦c⟧ = γ
    rw [hc]
  · rintro ⟨δ, rfl⟩
    have hp : phi n (FundamentalGroup.map (configProj n) (baseOrdered n) δ) = 1 := by
      refine phi_eq n ?_
      rw [one_smul]
      exact (congrArg Subtype.val
        ((configProj_isCoveringMap n).monodromy_map (FundamentalGroup.toPath δ))).symm
    show (phi n (FundamentalGroup.map (configProj n) (baseOrdered n) δ))⁻¹ = 1
    rw [hp, inv_one]

end Monodromy

end PermHomSol

theorem _root_.solution (n : ℕ) :
    ∃ nu : GeomBraidGroup n →* Equiv.Perm (Fin n),
      (∀ i : Fin (n - 1), nu (halfTwistBraid n i) =
          Equiv.swap (strandIdx i) (strandIdxSucc i)) ∧
        nu.ker = (FundamentalGroup.map (configProj n) (baseOrdered n)).range :=
  ⟨PermHomSol.nu n, PermHomSol.nu_halfTwist n, PermHomSol.nu_ker n⟩

#print axioms solution
