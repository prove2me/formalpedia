-- Prove2me | solution 1 for OAI.UniversalTensorSquare.candidate_kronecker_pos_of_subdiagram
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:37:03.049423+00:00
-- url     : https://prove2.me/submissions/285f973b-ecae-44ed-a603-0e61a9d2072a

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_Saxl_intertwiningLiftSubrep_injective
import Theorems.Thm_OAI_Saxl_pieri_strip_surjective_uts
import Theorems.Thm_OAI_UniversalTensorSquare_candidateHighWord_support

section
-- module Solutions.OAIQ259_US.Saxl_Basic
attribute [-instance] _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
theorem intertwining_finrank_pos_iff {G : Type uG} {V : Type uV} {W : Type uW} [Group G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    0 < Module.finrank ℂ (Representation.IntertwiningMap ρ σ) ↔
      ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 :=
  Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := Representation.IntertwiningMap ρ σ)

theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
    0 < kronecker a b t ↔
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        ((spechtRep a).tprod (spechtRep b)), f ≠ 0 := by
  exact @intertwining_finrank_pos_iff (Equiv.Perm (Fin n)) (Specht t)
    (Specht a ⊗[ℂ] Specht b) _ _ _ _ _ _ _
    (spechtRep t) ((spechtRep a).tprod (spechtRep b))

/- Column permutations cannot also fix the row word unless they are identity. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_HighProjection
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.Columns.columnTableau_val _root_.OAI.Saxl.coordinateProjection_apply _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.tableauInclusion_cell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/


lemma polytabloid_support {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) (ha : polytabloid t a ≠ 0) :
    ∃ g : columnGroup t, a = rowWord t ∘ (g : Equiv.Perm (Fin n)) := by
  classical
  have hex : ∃ g : columnGroup t, a ∘ (g : Equiv.Perm (Fin n)) = rowWord t := by
    by_contra! hh
    apply ha
    unfold polytabloid
    simp only [Finset.sum_apply, Pi.smul_apply, wordRep, MonoidHom.coe_mk,
      OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
    simp [hh]
  obtain ⟨g, hg⟩ := hex
  refine ⟨g⁻¹, ?_⟩
  funext i
  have he := congrFun hg ((g : Equiv.Perm (Fin n))⁻¹ i)
  simpa using he

/- Local same-high projection in the ordinary pair-letter coordinate space. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CoordinateSector
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/

lemma altWord_move {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (r : G) :
    altWord G (a ∘ (r : Equiv.Perm (Fin n))) =
      signC (r : Equiv.Perm (Fin n)) • altWord G a := by
  classical
  let := Fintype.ofFinite G
  have he : Pi.single (a ∘ (r : Equiv.Perm (Fin n))) (1 : ℂ) =
      wordRep n d (r⁻¹ : G) (Pi.single a 1) := by
    rw [wordRep_single]
    rfl
  unfold altWord
  rw [he]
  simp only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, Finset.smul_sum]
  apply (Equiv.sum_comp (Equiv.mulRight r) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC ((g*r : G) : Equiv.Perm (Fin n)) •
    wordRep n d (((g*r : G) : Equiv.Perm (Fin n)) * (r : Equiv.Perm (Fin n))⁻¹) (Pi.single a 1) = _
  simp only [Subgroup.coe_mul, map_mul, mul_inv_cancel_right, smul_smul]
  rw [mul_comm (signC (g : Equiv.Perm (Fin n)))]

/- Keeping a prescribed coloring restricts the alternating group to its
sector stabilizer. This is the finite coset calculation behind block-factorization. -/
theorem altWord_sector {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (Q : Fin d → Prop) (D : Fin n → Prop)
    (ha : ∀ i, Q (a i) ↔ D i) :
    coordinateProjection (fun b => ∀ i, Q (b i) ↔ D i) (altWord G a) =
      altWord (G ⊓ sectorGroup D) a := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite ↥(G ⊓ sectorGroup D)
  have hh (g : G) :
      (∀ i, Q ((a ∘ ((g : Equiv.Perm (Fin n))⁻¹ : Equiv.Perm (Fin n))) i) ↔ D i) ↔
        (g : Equiv.Perm (Fin n)) ∈ sectorGroup D := by
    constructor
    · intro h i
      have h' := (ha _).symm.trans (h ((g : Equiv.Perm (Fin n)) i))
      simpa using h'.symm
    · intro h i
      exact (ha _).trans (by simpa using (h (((g : Equiv.Perm (Fin n))⁻¹) i)).symm)
  unfold altWord
  simp only [map_sum, map_smul, wordRep_single, coordinateProjection_single, hh, smul_ite, smul_zero]
  let e : {g : G // (g : Equiv.Perm (Fin n)) ∈ sectorGroup D} ≃ ↥(G ⊓ sectorGroup D) := {
    toFun := fun g => ⟨g.val.val, g.val.property, g.property⟩
    invFun := fun g => ⟨⟨g.val, g.property.1⟩, g.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Finset.sum_filter]
  rw [← Finset.sum_attach]
  apply Fintype.sum_equiv ?_ _ _ ?_
  · exact (Equiv.subtypeEquivRight (fun g => by simp)).trans e
  · intro g
    rfl

end Saxl

namespace Saxl
/- The prescribed high sector in the actual staircase enumeration. -/

lemma coordinateProjection_tensor {n d e : ℕ}
    (P : (Fin n → Fin d) → Prop) (Q : (Fin n → Fin e) → Prop)
    (x : WordSpace n d) (y : WordSpace n e) :
    coordinateProjection (fun w => P (splitLeft w) ∧ Q (splitRight w))
      (wordTensor n d e (x ⊗ₜ[ℂ] y)) =
    wordTensor n d e (coordinateProjection P x ⊗ₜ[ℂ] coordinateProjection Q y) := by
  classical
  ext w
  by_cases hp : P (splitLeft w) <;> by_cases hq : Q (splitRight w) <;>
    simp [hp,hq]

lemma altWord_sector_rotated {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (Q : Fin d → Prop) (D : Fin n → Prop) (r : G)
    (ha : ∀ i, Q ((a ∘ (r : Equiv.Perm (Fin n))) i) ↔ D i) :
    coordinateProjection (fun b => ∀ i, Q (b i) ↔ D i) (altWord G a) =
      signC (r : Equiv.Perm (Fin n)) • altWord (G ⊓ sectorGroup D) (a ∘ (r : Equiv.Perm (Fin n))) := by
  have hh := altWord_sector G (a ∘ (r : Equiv.Perm (Fin n))) Q D ha
  rw [altWord_move, map_smul] at hh
  rw [← hh, smul_smul, signC_mul_self, one_smul]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PositionSplit
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.joinPositions_parts _root_.OAI.Saxl.leftWord_join _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.rightWord_join _root_.OAI.Saxl.sumPerm_mul _root_.OAI.Saxl.sumPerm_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/

lemma altWord_split_term {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w v : Fin n → Fin d) (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    (signC (sumPerm e g h) • wordRep n d (sumPerm e g h) (Pi.single w 1)) v =
    (signC g • wordRep a d g (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC h • wordRep b d h (Pi.single (rightWord e w) 1)) (rightWord e v) := by
  rw [single_positionProduct e w]
  change signC (sumPerm e g h) *
    ((Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e (v ∘ sumPerm e g h)) *
      (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e (v ∘ sumPerm e g h))) = _
  have h₁ : leftWord e (v ∘ sumPerm e g h) = leftWord e v ∘ g := by
    ext i; simp [leftWord]
  have h₂ : rightWord e (v ∘ sumPerm e g h) = rightWord e v ∘ h := by
    ext i; simp [rightWord]
  rw [h₁,h₂,signC_sumPerm]
  change _ = (signC g * (Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e v ∘ g)) *
    (signC h * (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e v ∘ h))
  ring

/- Independent block permutations factor with exactly the product sign. -/
theorem altWord_split {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (G : Subgroup (Equiv.Perm (Fin n))) (G₁ : Subgroup (Equiv.Perm (Fin a)))
    (G₂ : Subgroup (Equiv.Perm (Fin b))) (E : G ≃ G₁ × G₂)
    (hE : ∀ g : G, (g : Equiv.Perm (Fin n)) =
      sumPerm e ((E g).1 : Equiv.Perm (Fin a)) ((E g).2 : Equiv.Perm (Fin b)))
    (w : Fin n → Fin d) :
    altWord G w = positionProduct e (altWord G₁ (leftWord e w)) (altWord G₂ (rightWord e w)) := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite G₁
  let := Fintype.ofFinite G₂
  ext v
  unfold altWord
  simp only [Finset.sum_apply, positionProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : G₁ × G₂,
      (signC (p.1 : Equiv.Perm (Fin a)) • wordRep a d p.1 (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC (p.2 : Equiv.Perm (Fin b)) • wordRep b d p.2 (Pi.single (rightWord e w) 1)) (rightWord e v) := by
        apply Fintype.sum_equiv E
        intro g
        rw [hE g]
        exact altWord_split_term e w v _ _
    _ = _ := Fintype.sum_prod_type _



theorem altWord_fiber_split {n a b d : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b)
    (f : Fin n → α) (w : Fin n → Fin d) :
    altWord (fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) w =
      positionProduct e
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inl i)))) (leftWord e w))
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inr i)))) (rightWord e w)) := by
  apply altWord_split e _ _ _ (fiberSplit e f).symm
  intro g
  exact (congrArg Subtype.val ((fiberSplit e f).apply_symm_apply g)).symm


end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

/- Explicit finite-group induction on a linear map. -/

lemma averagedMap_apply {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) (f : X →ₗ[ℂ] Y) (x : X) :
    averagedMap ρ σ f x = ∑ g : G, σ g (f (ρ g⁻¹ x)) := by
  simp only [averagedMap, Representation.IntertwiningMap.coe_mk, LinearMap.sum_apply,
    LinearMap.comp_apply]

/- Coordinate-sector induction, in precisely the nonzero-Hom form used in
the staircase induction. The projector kills translates outside the stabilizer. -/
theorem sector_average_nonzero {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (H : Subgroup G) (f : X →ₗ[ℂ] Y) (hf : f ≠ 0)
    (he : ∀ g ∈ H, ∀ x, f (ρ g x) = σ g (f x))
    (P : Y →ₗ[ℂ] Y) (hP : ∀ x, P (f x) = f x)
    (hkill : ∀ g ∉ H, ∀ x, P (σ g (f x)) = 0) :
    averagedMap ρ σ f ≠ 0 := by
  classical
  have hproj (x : X) : P (averagedMap ρ σ f x) =
      ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) • f x := by
    rw [averagedMap_apply, map_sum]
    have hh (g : G) : P (σ g (f (ρ g⁻¹ x))) = if g ∈ H then f x else 0 := by
      by_cases hg : g ∈ H
      · rw [ite_eq_left hg, ← he g hg, ← Module.End.mul_apply, ← map_mul,
          mul_inv_cancel, map_one]
        exact hP x
      · rw [ite_eq_right hg]
        exact hkill g hg _
    simp only [hh]
    simp [Finset.sum_ite, Nat.cast_smul_eq_nsmul]
  have hc : ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact ne_of_gt (Finset.card_pos.mpr ⟨1, by simp⟩)
  intro hz
  apply hf
  ext x
  have heq := hproj x
  rw [hz] at heq
  change P 0 = _ at heq
  rw [map_zero] at heq
  exact (smul_eq_zero.mp heq.symm).resolve_left hc

open scoped MonoidAlgebra

end Saxl

namespace Saxl

theorem sector_support_transfer {n d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (D : Fin n → Prop) (A : Fin d → Prop) (z : WordSpace n d)
    (f : X →ₗ[ℂ] WordSpace n d) (hf : f ≠ 0)
    (he : ∀ g ∈ sectorGroup D, ∀ x, f (ρ g x) = wordRep n d g (f x))
    (hm : ∀ x, f x ∈ cyclic (wordRep n d) z)
    (hs : ∀ x w, f x w ≠ 0 → wordSector D A w) :
    ∃ F : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation,
      F ≠ 0 := by
  classical
  let P := coordinateProjection (wordSector D A)
  have hP (x) : P (f x) = f x := by
    ext w
    change (if wordSector D A w then f x w else 0) = _
    split_ifs with h
    · rfl
    · exact (not_ne_iff.mp (fun hh => h (hs x w hh))).symm
  have hk (g : Equiv.Perm (Fin n)) (hg : g ∉ sectorGroup D) (x) :
      P (wordRep n d g (f x)) = 0 := by
    ext w
    change (if wordSector D A w then f x (w ∘ g) else 0) = 0
    split_ifs with hw
    · by_contra hn
      have hh := hs x (w ∘ g) hn
      apply hg
      intro i
      exact (hw (g i)).symm.trans (hh i)
    · rfl
  let F := averagedMap ρ (wordRep n d) f
  have hF : F ≠ 0 := sector_average_nonzero ρ (wordRep n d) (sectorGroup D) f hf he P hP hk
  have hmem (x) : F x ∈ cyclic (wordRep n d) z := by
    rw [show F x = _ from averagedMap_apply ρ (wordRep n d) f x]
    apply Submodule.sum_mem
    intro g hg
    exact (cyclic (wordRep n d) z).apply_mem_toSubmodule g (hm _)
  let G : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation :=
    { toLinearMap := F.toLinearMap.codRestrict _ hmem
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact LinearMap.congr_fun (F.isIntertwining' g) x }
  refine ⟨G, ?_⟩
  intro hz
  apply hF
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun l => l x) hz)

theorem cyclic_projection_support {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ} [Group G] [Finite G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (v : X)
    (f : Representation.IntertwiningMap τ (cyclic σ (F v)).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap τ (cyclic ρ v).toRepresentation, g ≠ 0 := by
  obtain ⟨g,hg⟩ := intertwining_lift_surjective (cyclicMap F v) (cyclicMap_surjective F v) f
  refine ⟨g, ?_⟩
  intro hz
  apply hf
  rw [← hg,hz]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact map_zero (cyclicMap F v)



end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Coordinate subrepresentation using only letters with property A. -/

lemma alphabetSub_iff {n d : ℕ} (A : Fin d → Prop) (x : WordSpace n d) :
    x ∈ alphabetSub n d A ↔ ∀ w, x w ≠ 0 → ∀ i, A (w i) := by
  change (∀ w, (∃ i, ¬ A (w i)) → x w = 0) ↔ _
  constructor
  · intro h w hw i
    by_contra hn
    exact hw (h w ⟨i,hn⟩)
  · intro h w hw
    by_contra hn
    obtain ⟨i,hi⟩ := hw
    exact hi (h w hn i)

lemma cyclic_alphabet {n d : ℕ} (A : Fin d → Prop) (v : WordSpace n d)
    (hv : v ∈ alphabetSub n d A) (x : WordSpace n d) (hx : x ∈ cyclic (wordRep n d) v) :
    x ∈ alphabetSub n d A := (cyclic_le _ _ _).mpr hv hx

lemma single_mem_alphabet {n d : ℕ} (A : Fin d → Prop) (a : Fin n → Fin d) (ha : ∀ i, A (a i)) :
    (Pi.single a (1:ℂ) : WordSpace n d) ∈ alphabetSub n d A := by
  classical
  intro w hw
  apply Pi.single_eq_of_ne
  intro he
  subst w
  obtain ⟨i,hi⟩ := hw
  exact hi (ha i)

lemma altWord_mem_alphabet {n d : ℕ} (A : Fin d → Prop)
    (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n → Fin d) (ha : ∀ i, A (a i)) :
    altWord G a ∈ alphabetSub n d A := by
  classical
  unfold altWord
  apply Submodule.sum_mem
  intro g hg
  apply Submodule.smul_mem
  exact (alphabetSub n d A).apply_mem_toSubmodule g.val (single_mem_alphabet A a ha)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtClassification
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.tableauInclusion_cell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV uG

namespace Saxl

/- Rows enumerate exactly the actual cells, including the empty diagram. -/



lemma columnAlt_eq_zero_of_rows {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (hd : d < μ.colLen 0) : columnAlt (d := d) t = 0 := by
  classical
  have hz : ∀ a : Fin n → Fin d, columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
    intro a
    let j : Fin (μ.colLen 0) → Fin n := fun i => t.symm
      ⟨(i.val, 0), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩
    have hnot : ¬ Function.Injective (a ∘ j) := by
      intro hi
      have hh := Fintype.card_le_of_injective _ hi
      simp only [Fintype.card_fin] at hh
      omega
    simp only [Function.Injective] at hnot
    push Not at hnot
    obtain ⟨i, k, ha, hik⟩ := hnot
    have hj : j i ≠ j k := by
      intro he
      apply hik
      apply Fin.ext
      have hh := congrArg (fun l => (t l).val.1) he
      simpa [j] using hh
    exact columnAlt_collision t a (j i) (j k) hj (by simp [j]) ha
  apply LinearMap.ext
  intro x
  have he : x = ∑ a, x a • Pi.single a (1 : ℂ) := by
    ext b
    simp [Pi.single_apply]
  rw [he, map_sum]
  simp only [map_smul, hz, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

/- A Specht constituent of a `d`-letter position representation has at most
`d` rows, proved by the genuine first-column antisymmetrizer. -/
theorem specht_rows_of_hom {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep t) (wordRep n d)) (hf : f ≠ 0) :
    μ.colLen 0 ≤ d := by
  classical
  let := specht_irreducible t
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  by_contra h
  have hd : d < μ.colLen 0 := lt_of_not_ge h
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  have he := columnOperator_intertwining t f p
  change f (columnOperator t (spechtRep t) p) = columnAlt t (f p) at he
  rw [columnAlt_eq_zero_of_rows t hd, LinearMap.zero_apply] at he
  have hz : columnOperator t (spechtRep t) p = 0 := hi (he.trans (map_zero f).symm)
  exact columnAlt_polytabloid_ne_zero t
    ((columnOperator_subtype t (spechtSub t) p).symm.trans (congrArg Subtype.val hz))

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SupportSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uR uX uY uG uV

namespace Saxl

theorem word_support_separates {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ d →
      ∃ f : Representation.IntertwiningMap (spechtRep t) σ, f ≠ 0)
    (x : WordSpace n d) (hx : x ≠ 0) :
    ∃ f : Representation.IntertwiningMap (wordRep n d) σ, f x ≠ 0 := by
  apply intertwining_separates_of_simple_support (wordRep n d) σ ?_ x hx
  intro S hS
  let := hS
  obtain ⟨p, ⟨e⟩⟩ := irreducible_equiv_specht S.toRepresentation
  let t := partitionTableau p
  let i : Representation.IntertwiningMap (spechtRep t) (wordRep n d) :=
    (subrepInclusion S).comp e.symm.toIntertwiningMap
  have hi : i ≠ 0 := by
    intro he
    have hz := congrArg (fun F : Representation.IntertwiningMap (spechtRep t) (wordRep n d) =>
      F ⟨polytabloid t, mem_cyclic _ _⟩) he
    have h0 : e.symm ⟨polytabloid t, mem_cyclic _ _⟩ = 0 := Subtype.ext hz
    have h1 := e.symm.injective (h0.trans (map_zero _).symm)
    exact polytabloid_ne_zero t (congrArg Subtype.val h1)
  obtain ⟨f, hf⟩ := h _ t (specht_rows_of_hom t i hi)
  refine ⟨f.comp e.toIntertwiningMap, ?_⟩
  intro he
  apply hf
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  exact congrArg (fun F : Representation.IntertwiningMap S.toRepresentation σ => F z) he

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandOrbit
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma bandOrbitMap_base {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y)
    (hF : ∀ g : Equiv.Perm (Fin b), c ∘ g = c → ∀ x, F (ρ (sumPerm e 1 g) x) = F x)
    (x : X) : bandOrbitMap e ρ c F x c =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin b) => c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c)).card : ℂ) • F x := by
  classical
  change (∑ g : Equiv.Perm (Fin b), _) = _
  have hh (g : Equiv.Perm (Fin b)) :
      ((Pi.single (c ∘ (g⁻¹ : Equiv.Perm (Fin b))) (1:ℂ) : WordSpace b k) c) • F (ρ (sumPerm e 1 g⁻¹) x) =
      if c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c then F x else 0 := by
    by_cases h : c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c
    · rw [ite_eq_left h, h, Pi.single_eq_same, one_smul, hF g⁻¹ h]
    · rw [ite_eq_right h, Pi.single_eq_of_ne (Ne.symm h), zero_smul]
  simp only [hh]
  simp [Finset.sum_ite,Nat.cast_smul_eq_nsmul]

lemma bandOrbitMap_nonzero {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) (hF0 : F ≠ 0)
    (hF : ∀ g : Equiv.Perm (Fin b), c ∘ g = c → ∀ x, F (ρ (sumPerm e 1 g) x) = F x) :
    bandOrbitMap e ρ c F ≠ 0 := by
  classical
  intro hz
  apply hF0
  ext x
  have hh := bandOrbitMap_base e ρ c F hF x
  rw [hz] at hh
  change 0 = _ at hh
  have hc : ((Finset.univ.filter (fun g : Equiv.Perm (Fin b) =>
      c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact Finset.card_ne_zero.mpr ⟨1,Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  exact (smul_eq_zero.mp hh.symm).resolve_left hc

lemma bandOrbitMap_equivariant {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (τ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y)
    (hF : ∀ h : Equiv.Perm (Fin a), ∀ x, F (ρ (sumPerm e h 1) x) = τ h (F x))
    (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : X) (w : Fin b → Fin k) :
    bandOrbitMap e ρ c F (ρ (sumPerm e h q) x) w =
      τ h (bandOrbitMap e ρ c F x (w ∘ q)) := by
  classical
  change (∑ g : Equiv.Perm (Fin b), _) = τ h (∑ g : Equiv.Perm (Fin b), _)
  rw [map_sum]
  apply (Equiv.sum_comp (Equiv.mulLeft q) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  have he : sumPerm e 1 (q*g)⁻¹ * sumPerm e h q = sumPerm e h 1 * sumPerm e 1 g⁻¹ := by
    rw [← sumPerm_mul, ← sumPerm_mul]
    simp only [one_mul,mul_one,mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]
  change _ • F (ρ (sumPerm e 1 (q*g)⁻¹) (ρ (sumPerm e h q) x)) = _
  rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hF, map_smul]
  congr 1
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro hh
    funext i
    have hi := congrFun hh (q i)
    simpa using hi
  · intro hh
    funext i
    have hi := congrFun hh (q⁻¹ i)
    simpa using hi

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandGlue
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- Apply a band intertwiner to every scalar high-coordinate of a colored
strip orbit map. This is the concrete tensor product of the two maps. -/

lemma bandGlue_sum {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d) (x : X) :
    bandGlue e T L x = ∑ c : Fin b → Fin k, positionProduct e (T x c) (L (Pi.single c 1)) := by
  classical
  ext w
  change L (fun cb => T x cb (leftWord e w)) (rightWord e w) = _
  have he : (fun cb => T x cb (leftWord e w)) =
      ∑ c : Fin b → Fin k, T x c (leftWord e w) • (Pi.single c (1:ℂ) : WordSpace b k) := by
    ext c
    simp [Pi.single_apply]
  rw [he, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, positionProduct]

lemma bandGlue_equivariant {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (L : Representation.IntertwiningMap (wordRep b k) (wordRep b d))
    (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : X) :
    bandGlue e T L.toLinearMap (ρ (sumPerm e h q) x) =
      wordRep n d (sumPerm e h q) (bandGlue e T L.toLinearMap x) := by
  ext w
  change L (fun cb => T (ρ (sumPerm e h q) x) cb (leftWord e w)) (rightWord e w) = _
  simp only [hT]
  have he : (fun cb => (wordRep a d h (T x (cb ∘ q))) (leftWord e w)) =
      wordRep b k q (fun cb => T x cb ((leftWord e w) ∘ h)) := rfl
  rw [he]
  have hL : L (wordRep b k q (fun cb => T x cb ((leftWord e w) ∘ h))) =
      wordRep b d q (L (fun cb => T x cb ((leftWord e w) ∘ h))) :=
    LinearMap.congr_fun (L.isIntertwining' q) _
  rw [hL]
  change L (fun cb => T x cb ((leftWord e w) ∘ h)) ((rightWord e w) ∘ q) =
    L (fun cb => T x cb (leftWord e (w ∘ sumPerm e h q))) (rightWord e (w ∘ sumPerm e h q))
  have hl : leftWord e (w ∘ sumPerm e h q) = (leftWord e w) ∘ h := by
    funext i
    simp [leftWord,sumPerm_left]
  have hr : rightWord e (w ∘ sumPerm e h q) = (rightWord e w) ∘ q := by
    funext i
    simp [rightWord,sumPerm_right]
  rw [hl,hr]

lemma bandGlue_mem {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ x c, T x c ∈ cyclic (wordRep a d) v)
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d)
    (hL : ∀ y, L y ∈ cyclic (wordRep b d) u) (x : X) :
    bandGlue e T L x ∈ cyclic (wordRep n d) (positionProduct e v u) := by
  rw [bandGlue_sum]
  apply Submodule.sum_mem
  intro c hc
  exact product_mem_cyclic e v u _ _ (hT x c) (hL _)

/- A module containing every band Specht type of the relevant height detects
any nonzero high-valued colored-band vector. No multiplicity hypothesis is needed. -/

lemma positionProduct_sector {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (A : Fin d → Prop) (x : WordSpace a d) (y : WordSpace b d)
    (hx : x ∈ alphabetSub a d A) (hy : y ∈ alphabetSub b d (fun z => ¬A z)) :
    positionProduct e x y ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
  intro w hw
  by_contra hn
  apply hw
  have hxy : x (leftWord e w) ≠ 0 ∧ y (rightWord e w) ≠ 0 := mul_ne_zero_iff.mp hn
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j =>
    simpa only [Equiv.apply_symm_apply, Sum.isLeft_inl, iff_true,leftWord] using
      (alphabetSub_iff A x).mp hx _ hxy.1 j
  | inr j =>
    simpa only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, iff_false,rightWord] using
      (alphabetSub_iff (fun z => ¬A z) y).mp hy _ hxy.2 j

lemma bandGlue_sector {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (A : Fin d → Prop)
    (v : WordSpace a d) (u : WordSpace b d)
    (hv : v ∈ alphabetSub a d A) (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ x c, T x c ∈ cyclic (wordRep a d) v)
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d)
    (hL : ∀ y, L y ∈ cyclic (wordRep b d) u) (x : X) :
    bandGlue e T L x ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
  rw [bandGlue_sum]
  apply Submodule.sum_mem
  intro c hc
  apply positionProduct_sector
  · exact cyclic_alphabet A v hv _ (hT x c)
  · exact cyclic_alphabet (fun z => ¬A z) u hu _ (hL _)

theorem bandGlue_sector_exists {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hvA : v ∈ alphabetSub a d A)
    (huA : u ∈ alphabetSub b d (fun z => ¬A z))
    (hband : ∀ (μ : YoungDiagram) (t : Tableau b μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep b d) u).toRepresentation, f ≠ 0)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d)) (hT0 : T ≠ 0)
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (hTm : ∀ x c, T x c ∈ cyclic (wordRep a d) v) :
    ∃ f : X →ₗ[ℂ] WordSpace n d, f ≠ 0 ∧
      (∀ h q x, f (ρ (sumPerm e h q) x) = wordRep n d (sumPerm e h q) (f x)) ∧
      (∀ x, f x ∈ cyclic (wordRep n d) (positionProduct e v u)) ∧
      (∀ x, f x ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A)) := by
  classical
  obtain ⟨x,c,w,hxc⟩ : ∃ x c w, T x c w ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hT0
    ext x c w
    exact hh x c w
  have hv : (fun cb => T x cb w) ≠ (0 : WordSpace b k) := by
    intro hz
    exact hxc (congrFun hz c)
  obtain ⟨L,hL⟩ := word_support_separates (cyclic (wordRep b d) u).toRepresentation hband _ hv
  let L' := (subrepInclusion (cyclic (wordRep b d) u)).comp L
  have hL' : L' (fun cb => T x cb w) ≠ 0 := by
    intro hz
    apply hL
    exact Subtype.ext hz
  obtain ⟨z,hz⟩ : ∃ z, L' (fun cb => T x cb w) z ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hL' (funext hh)
  refine ⟨bandGlue e T L'.toLinearMap, ?_, bandGlue_equivariant e ρ T hT L', ?_, ?_⟩
  · intro he
    apply hz
    have hh := congrArg (fun f : X →ₗ[ℂ] WordSpace n d => f x (joinPositions e w z)) he
    change L' (fun cb => T x cb (leftWord e (joinPositions e w z))) (rightWord e (joinPositions e w z)) = 0 at hh
    simpa only [leftWord_join, rightWord_join] using hh
  · exact bandGlue_mem e v u T hTm L'.toLinearMap (fun y => (L y).property)

  · exact bandGlue_sector e A v u hvA huA T hTm L'.toLinearMap (fun y => (L y).property)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_StripExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma restrictPerm_apply {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin n))
    (hg : ∀ x, g x ∈ Set.range i ↔ x ∈ Set.range i) (k : Fin a) :
    i (restrictPerm i g hg k) = g (i k) := by
  change ((Equiv.ofInjective i i.injective)
    ((Equiv.ofInjective i i.injective).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma tableauInclusion_trans {a b n : ℕ} {ν η μ : YoungDiagram}
    (s : Tableau a ν) (u : Tableau b η) (t : Tableau n μ)
    (h₁ : ν ≤ η) (h₂ : η ≤ μ) (k : Fin a) :
    tableauInclusion u t h₂ (tableauInclusion s u h₁ k) =
      tableauInclusion s t (h₁.trans h₂) k := by
  change t.symm ⟨(u (u.symm ⟨(s k).val, _⟩)).val, _⟩ = t.symm ⟨(s k).val, _⟩
  simp only [Equiv.apply_symm_apply]

lemma extendColor_apply {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (x : Fin a) : extendColor i c q (i x) = c x := by
  classical
  unfold extendColor
  rw [dite_eq_left ⟨x,rfl⟩]
  congr 1
  exact (Equiv.ofInjective i i.injective).symm_apply_apply x

lemma extendColor_mem {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) (x : Fin n) :
    extendColor i c (q+1) x ≤ q ↔ x ∈ Set.range i := by
  classical
  unfold extendColor
  split_ifs with h
  · exact iff_of_true (hc _) h
  · simp [h]

lemma extendColor_le {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) (x : Fin n) : extendColor i c (q+1) x ≤ q+1 := by
  classical
  unfold extendColor
  split_ifs
  · exact (hc _).trans (Nat.le_succ q)
  · exact le_rfl

lemma extendColor_count_old {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q j : ℕ)
    (hj : j ≠ q) :
    (Finset.univ.filter (fun x => extendColor i c q x = j)).card =
      (Finset.univ.filter (fun x => c x = j)).card := by
  classical
  symm
  apply Finset.card_bij (fun x _ => i x)
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, extendColor_apply] using hx
  · intro x hx y hy hxy
    exact i.injective hxy
  · intro y hy
    have hyj := (Finset.mem_filter.mp hy).2
    have hym : y ∈ Set.range i := by
      by_contra hn
      simp only [extendColor, dite_eq_right hn] at hyj
      exact hj hyj.symm
    obtain ⟨x,rfl⟩ := hym
    refine ⟨x, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, extendColor_apply] using hyj

lemma extendColor_count_new {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) :
    (Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1)).card = n-a := by
  classical
  have he : Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1) =
      Finset.univ \ Finset.univ.map i := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_map]
    change extendColor i c (q+1) x = q+1 ↔ ¬ x ∈ Set.range i
    rw [← extendColor_mem i c q hc x]
    have hl := extendColor_le i c q hc x
    omega
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SizedStrips
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl



theorem stripChain_restriction_any {bs ν μ} (hs : SizedStripChain bs ν μ)
    {a n : ℕ} (s : Tableau a ν) (t : Tableau n μ) :
    ∃ (c : Fin n → ℕ) (F : Specht t →ₗ[ℂ] Specht s),
      Function.Surjective F ∧
      (∀ i, c i ≤ bs.length) ∧
      (∀ i, c i = 0 ↔ i ∈ Set.range (tableauInclusion s t hs.le)) ∧
      (∀ j (hj : j < bs.length), (Finset.univ.filter (fun i => c i = j+1)).card = bs[j]) ∧
      (∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ i, c (g i) = c i) →
        (∀ k, g (tableauInclusion s t hs.le k) =
          tableauInclusion s t hs.le (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x)) := by
  classical
  induction hs generalizing a n with
  | nil ν =>
    obtain ⟨F,hF,hFe⟩ := pieri_strip_surjective_uts s t
      (show HorizontalStrip ν ν from ⟨le_rfl, by intros x hx hn; exact False.elim (hn hx)⟩)
    refine ⟨fun _ => 0, F, hF, by simp, ?_, ?_, ?_⟩
    · intro i
      constructor
      · intro _
        refine ⟨s.symm (t i), ?_⟩
        change t.symm ⟨(s (s.symm (t i))).val, _⟩ = i
        simp only [Equiv.apply_symm_apply]
        exact t.symm_apply_apply i
      · intro _; rfl
    · intro j hj; simp at hj
    · intro g h hc he x
      exact hFe g h he x
  | @snoc bs ν η μ b hs hh hcard ih =>
    obtain ⟨c,F,hF,hc,hzero,hcount,he⟩ := ih s (shapeTableau η)
    obtain ⟨P,hP,hPe⟩ := pieri_strip_surjective_uts (shapeTableau η) t hh
    let i := tableauInclusion (shapeTableau η) t hh.1
    let c' := extendColor i c (bs.length+1)
    refine ⟨c', F.comp P, hF.comp hP, ?_, ?_, ?_, ?_⟩
    · intro k
      simpa only [List.length_append, List.length_singleton] using extendColor_le i c bs.length hc k
    · intro k
      constructor
      · intro hk
        change extendColor i c (bs.length+1) k = 0 at hk
        have hr : k ∈ Set.range i := (extendColor_mem i c bs.length hc k).mp (by omega)
        obtain ⟨l,rfl⟩ := hr
        have hl : c l = 0 := (extendColor_apply i c _ l).symm.trans hk
        obtain ⟨j,hj⟩ := (hzero l).mp hl
        refine ⟨j, ?_⟩
        rw [← tableauInclusion_trans s (shapeTableau η) t hs.le hh.1]
        exact congrArg i hj
      · rintro ⟨j,rfl⟩
        rw [← tableauInclusion_trans s (shapeTableau η) t hs.le hh.1]
        change extendColor i c _ (i _) = 0
        rw [extendColor_apply]
        exact (hzero _).mpr ⟨j,rfl⟩
    · intro j hj
      have hjle : j ≤ bs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      rcases lt_or_eq_of_le hjle with hjlt | rfl
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = j+1)).card = _
        rw [extendColor_count_old i c (bs.length+1) (j+1) (by omega), hcount j hjlt,
          List.getElem_append_left hjlt]
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = bs.length+1)).card = _
        rw [extendColor_count_new i c bs.length hc]
        simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        have ht : n = μ.card := by
          have := Fintype.card_congr t
          simpa only [Fintype.card_fin, Fintype.card_coe] using this
        omega
    · intro g h hg hgi x
      have hgmem : ∀ k, g k ∈ Set.range i ↔ k ∈ Set.range i := by
        intro k
        rw [← extendColor_mem i c bs.length hc, ← extendColor_mem i c bs.length hc]
        exact (congrArg (fun c => c ≤ bs.length) (hg k)).to_iff
      let k := restrictPerm i g hgmem
      have hik (l) : i (k l) = g (i l) := restrictPerm_apply i g hgmem l
      have hkcolor (l) : c (k l) = c l := by
        rw [← extendColor_apply i c (bs.length+1) (k l), hik, ← extendColor_apply i c (bs.length+1) l]
        exact hg (i l)
      have hkbase (l) : k (tableauInclusion s (shapeTableau η) hs.le l) =
          tableauInclusion s (shapeTableau η) hs.le (h l) := by
        apply i.injective
        rw [hik]
        change g (tableauInclusion (shapeTableau η) t hh.1 _) =
          tableauInclusion (shapeTableau η) t hh.1 _
        rw [tableauInclusion_trans, tableauInclusion_trans]
        exact hgi l
      change F (P (spechtRep t g x)) = _
      rw [hPe g k (fun l => (hik l).symm), he k h hkcolor hkbase]
      rfl

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_StripSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Place the smaller tableau on any chosen block, with the remaining strip
colors on its complement. No transitivity or induction rule is assumed. -/
theorem placed_strip_restriction {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ (c : Fin b → Fin bs.length) (F : Specht t →ₗ[ℂ] Specht s), Function.Surjective F ∧
      ∀ (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)), c ∘ q = c →
        ∀ x, F (spechtRep t (sumPerm e h q) x) = spechtRep s h (F x) := by
  classical
  obtain ⟨c,F,hF,hcb,hcz,hcount,hFe⟩ := stripChain_restriction_any hs s t
  let i := tableauInclusion s t hs.le
  let l : Fin a → Fin n := fun j => e.symm (Sum.inl j)
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair l i
    (fun x y h => Sum.inl.inj (e.symm.injective h)) i.injective
  have hcL (j : Fin a) : c (p (e.symm (Sum.inl j))) = 0 := by
    rw [show p (e.symm (Sum.inl j)) = i j from hp j]
    exact (hcz _).mpr ⟨j,rfl⟩
  have hcRpos (j : Fin b) : 0 < c (p (e.symm (Sum.inr j))) := by
    by_contra hn
    have hz : c (p (e.symm (Sum.inr j))) = 0 := by omega
    obtain ⟨k,hk⟩ := (hcz _).mp hz
    have hh : e.symm (Sum.inl k) = e.symm (Sum.inr j) := p.injective ((hp k).trans hk)
    have := e.symm.injective hh
    cases this
  let cb : Fin b → Fin bs.length := fun j => ⟨c (p (e.symm (Sum.inr j)))-1, by
    have := hcRpos j
    have := hcb (p (e.symm (Sum.inr j)))
    omega⟩
  have hcR (j : Fin b) : c (p (e.symm (Sum.inr j))) = (cb j).val+1 := by
    have := hcRpos j
    change _ = (c (p (e.symm (Sum.inr j)))-1)+1
    omega
  let F' := F.comp (spechtRep t p)
  have hP : Function.Surjective (spechtRep t p) := by
    intro x
    refine ⟨spechtRep t p⁻¹ x, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨cb,F',hF.comp hP, ?_⟩
  intro h q hq x
  let g := p * sumPerm e h q * p⁻¹
  have hgL (j : Fin a) : g (p (e.symm (Sum.inl j))) = p (e.symm (Sum.inl (h j))) := by
    simp [g]
  have hgR (j : Fin b) : g (p (e.symm (Sum.inr j))) = p (e.symm (Sum.inr (q j))) := by
    simp [g]
  have hgc (j : Fin n) : c (g j) = c j := by
    obtain ⟨z,rfl⟩ := p.surjective j
    obtain ⟨z,rfl⟩ := e.symm.surjective z
    cases z with
    | inl j => rw [hgL,hcL,hcL]
    | inr j =>
      rw [hgR,hcR,hcR]
      exact congrArg (fun x : Fin bs.length => x.val+1) (congrFun hq j)
  have hgi (j : Fin a) : g (i j) = i (h j) := by rw [← hp j,← hp (h j)]; exact hgL j
  change F (spechtRep t p (spechtRep t (sumPerm e h q) x)) = spechtRep s h (F (spechtRep t p x))
  have hmul : p * sumPerm e h q = g * p := by simp [g,mul_assoc]
  rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]
  exact hFe g h hgc hgi _

end Saxl

namespace Saxl

/- Required support transfer from a genuine iterated horizontal-strip
restriction and genuine independent high/band cyclic factors. -/
theorem strip_product_support {n a b d : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (f : Representation.IntertwiningMap (spechtRep s) (cyclic (wordRep a d) v).toRepresentation)
    (hf : f ≠ 0)
    (hband : ∀ (η : YoungDiagram) (r : Tableau b η), η.colLen 0 ≤ bs.length →
      ∃ F : Representation.IntertwiningMap (spechtRep r) (cyclic (wordRep b d) u).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, F ≠ 0 := by
  classical
  obtain ⟨c,F,hF,hFe⟩ := placed_strip_restriction hs s t e
  let G := (subrepInclusion (cyclic (wordRep a d) v)).comp f
  let F₀ : Specht t →ₗ[ℂ] WordSpace a d := G.toLinearMap.comp F
  have hF₀ : F₀ ≠ 0 := by
    intro hz
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := hF y
    apply Subtype.ext
    exact LinearMap.congr_fun hz x
  have hFb (q : Equiv.Perm (Fin b)) (hq : c ∘ q = c) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e 1 q) x) = F₀ x := by
    change G (F (spechtRep t (sumPerm e 1 q) x)) = G (F x)
    rw [hFe 1 q hq, map_one]
    rfl
  have hFa (h : Equiv.Perm (Fin a)) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e h 1) x) = wordRep a d h (F₀ x) := by
    change G (F (spechtRep t (sumPerm e h 1) x)) = wordRep a d h (G (F x))
    rw [hFe h 1 rfl]
    exact LinearMap.congr_fun (G.isIntertwining' h) (F x)
  let T := bandOrbitMap e (spechtRep t) c F₀
  have hTm (x : Specht t) (w : Fin b → Fin bs.length) : T x w ∈ cyclic (wordRep a d) v := by
    change (∑ g : Equiv.Perm (Fin b), _) ∈ (cyclic (wordRep a d) v).toSubmodule
    apply Submodule.sum_mem
    intro g hg
    apply Submodule.smul_mem
    exact (f (F (spechtRep t (sumPerm e 1 g⁻¹) x))).property
  obtain ⟨L,hL,hLe,hLm,hLs⟩ := bandGlue_sector_exists e (spechtRep t) v u A hv hu hband T
    (bandOrbitMap_nonzero e (spechtRep t) c F₀ hF₀ hFb)
    (bandOrbitMap_equivariant e (spechtRep t) (wordRep a d) c F₀ hFa) hTm
  apply sector_support_transfer (spechtRep t) (fun i => (e i).isLeft = true) A
    (positionProduct e v u) L hL _ hLm
  · intro x w hw
    by_contra hn
    exact hw (hLs x w hn)
  · intro g hg x
    let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g,hg⟩
    have heq : sumPerm e (leftRestriction e g') (rightRestriction e g') = g := sumPerm_restrictions e g'
    rw [← heq]
    exact hLe _ _ x

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SquareDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma spechtTensorMap_injective {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) : Function.Injective (spechtTensorMap a b) := by
  unfold spechtTensorMap
  apply (wordTensor _ _ _).injective.comp
  exact TensorProduct.map_injective_of_flat_flat _ _
    (spechtSub a).toSubmodule.subtype_injective (spechtSub b).toSubmodule.subtype_injective

lemma polytabloidTensor_cyclic_le_range {n : ℕ} {α β : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) :
    cyclic (wordRep n (α.colLen 0 * β.colLen 0))
      (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≤
        (spechtTensorMap a b).range := by
  unfold spechtTensorMap
  apply (cyclic_le _ _ _).mpr
  exact ⟨(⟨polytabloid a', polytabloid_mem_all a a'⟩ : Specht a) ⊗ₜ[ℂ]
    (⟨polytabloid b', polytabloid_mem_all b b'⟩ : Specht b), rfl⟩

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_MarkedTriangle
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.UniversalTensorSquare.candidateRotateCol_col _root_.OAI.UniversalTensorSquare.candidateRotateRow_row _root_.OAI.UniversalTensorSquare.candidateRowShuffle_row _root_.OAI.UniversalTensorSquare.candidateSeparatedRow_row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked Triangle. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl

theorem candidate_marked_rigidity (M b δ : ℕ) (hM : 4 ≤ M)
    (g k : Equiv.Perm (candidate M b δ).cells)
    (hg : ∀ x, (g x).val.1 = x.val.1)
    (hk : ∀ x, (k x).val.2 = x.val.2)
    (hc : ∀ x, candidateMark M b (g x).val.2 ↔ candidateMark M b (k x).val.1) :
    ∀ x, candidateMark M b (g x).val.2 ↔ x.val.1 + x.val.2 < M-2 := by
  classical
  let A : Finset (candidate M b δ).cells :=
    Finset.univ.filter (fun x => candidateMark M b (g x).val.2)
  let B : Finset (candidate M b δ).cells :=
    Finset.univ.filter (fun x => x.val.1 + x.val.2 < M-2)
  let eR : A ≃ (staircase (M-2)).cells :=
    (Equiv.subtypeEquiv g (by intro x; simp only [A, Finset.mem_filter,
      Finset.mem_univ, true_and])).trans (markedRowEquiv M b δ hM)
  let eC : A ≃ (staircase (M-2)).cells :=
    (Equiv.subtypeEquiv k (by
      intro x
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hc x)).trans (markedColEquiv M b δ hM)
  let eB : B ≃ (staircase (M-2)).cells :=
    { toFun := fun x => ⟨x.val.val, mem_staircase.mpr (by simpa [B] using x.property)⟩
      invFun := fun x => ⟨⟨x.val, mem_candidate.mpr (Or.inl (by
        have hx := mem_staircase.mp x.property; omega))⟩,
        by simp [B, mem_staircase.mp x.property]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : A.card = B.card := by
    have he := Fintype.card_congr (eR.trans eB.symm)
    simpa using he
  have hrow : ∑ x ∈ A, (x.val.1 : ℤ) = ∑ x ∈ B, (x.val.1 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hR := Equiv.sum_comp eR (fun x => (x.val.1 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.1 : ℤ))
    simpa [eR, eB, markedRowEquiv, hg] using hR.trans hB.symm
  have hcol : ∑ x ∈ A, (x.val.2 : ℤ) = ∑ x ∈ B, (x.val.2 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hC := Equiv.sum_comp eC (fun x => (x.val.2 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.2 : ℤ))
    simpa [eC, eB, markedColEquiv, hk] using hC.trans hB.symm
  let w := fun x : (candidate M b δ).cells =>
    2 * ((M-2 : ℕ) : ℤ) - 1 - 2 * (x.val.1 : ℤ) - 2 * (x.val.2 : ℤ)
  have he : ∑ x ∈ A, w x = ∑ x ∈ B, w x := by
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    rw [hcard, hrow, hcol]
  have hab := finset_eq_of_signed_sum A B w
    (fun x hx => by
      have hh : x.val.1 + x.val.2 < M-2 := by simpa [B] using hx
      dsimp [w]; omega)
    (fun x hx => by
      have hh : ¬x.val.1 + x.val.2 < M-2 := by simpa [B] using hx
      dsimp [w]; omega) he
  intro x
  have := Finset.ext_iff.mp hab x
  simpa [A, B] using this

end UniversalTensorSquare

namespace UniversalTensorSquare
open Saxl

theorem candidate_projected_marked_positions {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ))
    (w : Fin n → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0))
    (hw : sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) w ≠ 0) :
    ∀ i, candidateMark M b (splitLeft w i).val ↔ candidateTriangle t i := by
  classical
  have heq : ∀ i, candidateMark M b (splitLeft w i).val ↔
      candidateMark M b (splitRight w i).val := by
    by_contra hh
    apply hw
    simp [sameMarkProjection, hh]
  have hww : rowColumnWord t w ≠ 0 := by
    simpa [sameMarkProjection, heq] using hw
  have hp : polytabloid (transposeTableau t) (splitLeft w) *
      polytabloid t (splitRight w) ≠ 0 := by
    simpa only [rowColumnWord, wordTensor_tmul] using hww
  obtain ⟨g, hg⟩ := polytabloid_support (transposeTableau t) _ (mul_ne_zero_iff.mp hp).1
  obtain ⟨k, hk⟩ := polytabloid_support t _ (mul_ne_zero_iff.mp hp).2
  let gc : Equiv.Perm (candidate M b δ).cells := (t.symm.trans (g : Equiv.Perm _)).trans t
  let kc : Equiv.Perm (candidate M b δ).cells := (t.symm.trans (k : Equiv.Perm _)).trans t
  have hgc : ∀ x, (gc x).val.1 = x.val.1 := by
    intro x
    have hh := g.property (t.symm x)
    change (t ((g : Equiv.Perm _) (t.symm x))).val.1 = (t (t.symm x)).val.1 at hh
    simpa [gc] using hh
  have hkc : ∀ x, (kc x).val.2 = x.val.2 := by
    intro x
    have hh := k.property (t.symm x)
    change (t ((k : Equiv.Perm _) (t.symm x))).val.2 = (t (t.symm x)).val.2 at hh
    simpa [kc] using hh
  have hcommon : ∀ x, candidateMark M b (gc x).val.2 ↔ candidateMark M b (kc x).val.1 := by
    intro x
    have hh := heq (t.symm x)
    rw [hg, hk] at hh
    exact hh
  have hr := candidate_marked_rigidity M b δ hM gc kc hgc hkc hcommon
  intro i
  have hh := hr (t i)
  rw [hg]
  simpa [gc, rowWord, transposeTableau, candidateTriangle] using hh

theorem candidate_projected_sector {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) =
      coordinateProjection (fun w =>
        (∀ i, candidateMark M b (splitLeft w i).val ↔ candidateTriangle t i) ∧
        (∀ i, candidateMark M b (splitRight w i).val ↔ candidateTriangle t i))
        (rowColumnWord t) := by
  classical
  ext w
  by_cases he : ∀ i, candidateMark M b (splitLeft w i).val ↔
      candidateMark M b (splitRight w i).val
  · by_cases hw : sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) w = 0
    · have hw' : rowColumnWord t w = 0 := by simpa [sameMarkProjection, he] using hw
      simp [hw, hw']
    · have hD := candidate_projected_marked_positions hM t w hw
      have hD' : ∀ i, candidateMark M b (splitRight w i).val ↔ candidateTriangle t i :=
        fun i => (he i).symm.trans (hD i)
      simp [sameMarkProjection, he, hD']
  · have hn : ¬ ((∀ i, candidateMark M b (splitLeft w i).val ↔ candidateTriangle t i) ∧
        (∀ i, candidateMark M b (splitRight w i).val ↔ candidateTriangle t i)) := by
      rintro ⟨h₁,h₂⟩
      exact he (fun i => (h₁ i).trans (h₂ i).symm)
    simp [sameMarkProjection, he, hn]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CandidateRotation
attribute [-simp] _root_.OAI.UniversalTensorSquare.candidateRowShuffle_row _root_.OAI.UniversalTensorSquare.candidateSeparatedRow_row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Rotation. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateRotateRow_mark (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    candidateMark M b (candidateRotateRow M b δ hM x).val.2 ↔
      x.val.1 + x.val.2 < M-2 := by
  have hx := mem_candidate.mp x.property
  change candidateMark M b
    (if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
      (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)
    else (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)) ↔ _
  rcases x with ⟨⟨i,j⟩, hx0⟩
  dsimp only at *
  simp only [candidateMark, Equiv.swap_apply_def]
  split_ifs <;> omega

lemma candidateRotateCol_mark (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    candidateMark M b (candidateRotateCol M b δ hM x).val.1 ↔
      x.val.1 + x.val.2 < M-2 := by
  have hh := candidateRotateRow_mark M b δ hM (candidateSwap M b δ x)
  change candidateMark M b (candidateRotateRow M b δ hM (candidateSwap M b δ x)).val.2 ↔ _
  simpa [candidateSwap, Nat.add_comm] using hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CandidateCut
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.UniversalTensorSquare.candidateRowShuffle_row _root_.OAI.UniversalTensorSquare.candidateSeparatedRow_row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Cut. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl

lemma candidateRotatePositions_sign {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    signC (candidateRotateColPositions hM t : Equiv.Perm (Fin n)) =
      signC (candidateRotateRowPositions hM t : Equiv.Perm (Fin n)) := by
  let q : Equiv.Perm (Fin n) := (t.trans (candidateSwap M b δ)).trans t.symm
  have he : (candidateRotateColPositions hM t : Equiv.Perm (Fin n)) =
      q * (candidateRotateRowPositions hM t : Equiv.Perm (Fin n)) * q := by
    ext i
    simp [q, candidateRotateColPositions, candidateRotateRowPositions, candidateRotateCol]
  rw [he, map_mul, map_mul]
  calc
    signC q * signC (candidateRotateRowPositions hM t : Equiv.Perm (Fin n)) * signC q =
      signC (candidateRotateRowPositions hM t : Equiv.Perm (Fin n)) * (signC q * signC q) := by ring
    _ = _ := by rw [signC_mul_self, mul_one]

theorem candidate_cut_layers {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) =
      wordTensor _ _ _ (candidateCutRow hM t ⊗ₜ[ℂ] candidateCutCol hM t) := by
  rw [candidate_projected_sector hM, rowColumnWord]
  rw [coordinateProjection_tensor
    (fun a : Fin n → Fin ((candidate M b δ).transpose.colLen 0) =>
      ∀ i, candidateMark M b (a i).val ↔ candidateTriangle t i)
    (fun a : Fin n → Fin ((candidate M b δ).colLen 0) =>
      ∀ i, candidateMark M b (a i).val ↔ candidateTriangle t i)]
  have hr := altWord_sector_rotated (columnGroup (transposeTableau t))
    (rowWord (transposeTableau t)) (fun a => candidateMark M b a.val) (candidateTriangle t)
    (candidateRotateRowPositions hM t) (by
      intro i
      simpa [rowWord, transposeTableau, candidateRotateRowPositions, candidateTriangle] using
        candidateRotateRow_mark M b δ hM (t i))
  have hc := altWord_sector_rotated (columnGroup t)
    (rowWord t) (fun a => candidateMark M b a.val) (candidateTriangle t)
    (candidateRotateColPositions hM t) (by
      intro i
      simpa [rowWord, candidateRotateColPositions, candidateTriangle] using
        candidateRotateCol_mark M b δ hM (t i))
  rw [polytabloid_eq_altWord, polytabloid_eq_altWord, hr, hc,
    TensorProduct.smul_tmul_smul, candidateRotatePositions_sign, signC_mul_self, one_smul]
  rfl

lemma candidateCutPositions_left {n M b δ : ℕ} (t : Tableau n (candidate M b δ))
    (i : Fin (staircase (M-2)).card) :
    (t ((candidateCutPositions t).symm (Sum.inl i))).val = (stairTableau (M-2) i).val := by
  classical
  simp [candidateCutPositions, Equiv.sumCompl, candidateHighPositions]

lemma candidateRotateRow_triangle {M b δ : ℕ} (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) (hx : x.val.1 + x.val.2 < M-2) :
    (candidateRotateRow M b δ hM x).val.2 =
      if x.val.2 = M-3 then M+b-1 else x.val.2+2 := by
  change (if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
      (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)
    else (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)) = _
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

lemma candidateRotateCol_triangle {M b δ : ℕ} (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) (hx : x.val.1 + x.val.2 < M-2) :
    (candidateRotateCol M b δ hM x).val.1 =
      if x.val.1 = M-3 then M+b-1 else x.val.1+2 := by
  exact candidateRotateRow_triangle hM (candidateSwap M b δ x) (by
    change x.val.2 + x.val.1 < M-2
    omega)

lemma candidate_highRow_word {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    leftWord (candidateCutPositions t)
      (rowWord (transposeTableau t) ∘ (candidateRotateRowPositions hM t : Equiv.Perm (Fin n))) =
      candidateHighRowLetter M b δ hM ∘ rowWord (stairRowTableau (M-2)) := by
  funext i
  apply Fin.ext
  have hi := mem_staircase.mp (stairTableau (M-2) i).property
  have he := candidateCutPositions_left t i
  simp only [leftWord, Function.comp_apply, rowWord, stairRowTableau, transposeTableau,
    candidateRotateRowPositions, Equiv.trans_apply, Equiv.apply_symm_apply,
    staircaseSwap, candidateHighRowLetter, candidateHighLetter, Fin.val_cast]
  change (candidateRotateRow M b δ hM (t ((candidateCutPositions t).symm (Sum.inl i)))).val.2 = _
  rw [candidateRotateRow_triangle hM _ (by rw [he]; exact hi), he]
  rfl

lemma candidate_highCol_word {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    leftWord (candidateCutPositions t)
      (rowWord t ∘ (candidateRotateColPositions hM t : Equiv.Perm (Fin n))) =
      candidateHighLetter M b δ hM ∘ rowWord (stairTableau (M-2)) := by
  funext i
  apply Fin.ext
  have hi := mem_staircase.mp (stairTableau (M-2) i).property
  have he := candidateCutPositions_left t i
  simp only [leftWord, Function.comp_apply, rowWord, candidateRotateColPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, candidateHighLetter]
  change (candidateRotateCol M b δ hM (t ((candidateCutPositions t).symm (Sum.inl i)))).val.1 = _
  rw [candidateRotateCol_triangle hM _ (by rw [he]; exact hi), he]
  rfl

lemma candidate_row_cut_group {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) :
    columnGroup (transposeTableau t) ⊓ sectorGroup (candidateTriangle t) =
      fiberGroup (fun i => (t i).val.1) ⊓
        sectorGroup (fun i => (candidateCutPositions t i).isLeft = true) := by
  congr 1
  congr 1
  funext i
  exact propext (candidateCutPositions_high t i).symm

lemma candidate_col_cut_group {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) :
    columnGroup t ⊓ sectorGroup (candidateTriangle t) =
      fiberGroup (fun i => (t i).val.2) ⊓
        sectorGroup (fun i => (candidateCutPositions t i).isLeft = true) := by
  congr 1
  congr 1
  funext i
  exact propext (candidateCutPositions_high t i).symm

theorem candidateCutRow_factor {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    candidateCutRow hM t = positionProduct (candidateCutPositions t)
      (letterLift (candidateHighRowLetter M b δ hM) (polytabloid (stairRowTableau (M-2))))
      (candidateBandRow hM t) := by
  unfold candidateCutRow
  rw [candidate_row_cut_group, altWord_fiber_split]
  congr 1
  rw [candidate_highRow_word, polytabloid_eq_altWord, letterLift_altWord]
  congr 1
  change fiberGroup _ = fiberGroup (fun i => (stairTableau (M-2) i).val.1)
  congr 1
  funext i
  exact congrArg Prod.fst (candidateCutPositions_left t i)

theorem candidateCutCol_factor {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    candidateCutCol hM t = positionProduct (candidateCutPositions t)
      (letterLift (candidateHighLetter M b δ hM) (polytabloid (stairTableau (M-2))))
      (candidateBandCol hM t) := by
  unfold candidateCutCol
  rw [candidate_col_cut_group, altWord_fiber_split]
  congr 1
  rw [candidate_highCol_word, polytabloid_eq_altWord, letterLift_altWord]
  congr 1
  change fiberGroup _ = fiberGroup (fun i => (stairTableau (M-2) i).val.2)
  congr 1
  funext i
  exact congrArg Prod.snd (candidateCutPositions_left t i)

theorem candidate_cut_factor {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) =
      positionProduct (candidateCutPositions t) (candidateHighWord M b δ hM)
        (candidateBandWord hM t) := by
  rw [candidate_cut_layers, candidateCutRow_factor, candidateCutCol_factor]
  unfold candidateHighWord candidateHighMap staircaseWord
  rw [pairWordMap_tensor]
  ext w
  simp only [wordTensor_tmul, candidateBandWord, positionProduct]
  exact mul_mul_mul_comm _ _ _ _

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CandidateSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply _root_.OAI.UniversalTensorSquare.candidateRowShuffle_row _root_.OAI.UniversalTensorSquare.candidateSeparatedRow_row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Support. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem kronecker_pos_of_tensor_cyclic_support {n : ℕ} {α β μ : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n (α.colLen 0 * β.colLen 0))
        (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b'))).toRepresentation)
    (hf : f ≠ 0) : 0 < kronecker a b t := by
  let S := cyclic (wordRep n (α.colLen 0 * β.colLen 0))
    (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b'))
  let F := @intertwiningLiftSubrep (Equiv.Perm (Fin n))
    (Specht a ⊗[ℂ] Specht b) (WordSpace n (α.colLen 0 * β.colLen 0))
    _ _ _ _ _ ((spechtRep a).tprod (spechtRep b))
    (wordRep n (α.colLen 0 * β.colLen 0))
    (spechtTensorMap a b) (spechtTensorMap_injective a b)
    S (polytabloidTensor_cyclic_le_range a a' b b')
  have hF : Function.Injective F := @intertwiningLiftSubrep_injective (Equiv.Perm (Fin n))
    (Specht a ⊗[ℂ] Specht b) (WordSpace n (α.colLen 0 * β.colLen 0))
    _ _ _ _ _ ((spechtRep a).tprod (spechtRep b))
    (wordRep n (α.colLen 0 * β.colLen 0))
    (spechtTensorMap a b) (spechtTensorMap_injective a b)
    S (polytabloidTensor_cyclic_le_range a a' b b')
  apply (kronecker_pos_iff a b t).mpr
  refine ⟨F.comp f, ?_⟩
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have he := congrArg (fun H => H x) hz
  change F (f x) = 0 at he
  change F (f x) = F 0
  simpa only [map_zero] using he

lemma pairWord_mem_alphabetLeft_gen {n a b : ℕ} (A : Fin a → Prop)
    (x : WordSpace n a) (y : WordSpace n b) (hx : x ∈ alphabetSub n a A) :
    wordTensor n a b (x ⊗ₜ[ℂ] y) ∈
      alphabetSub n (a*b) (fun c => A (finProdFinEquiv.symm c).1) := by
  apply (alphabetSub_iff _ _).mpr
  intro w hw i
  rw [wordTensor_tmul] at hw
  exact (alphabetSub_iff A x).mp hx (splitLeft w) (mul_ne_zero_iff.mp hw).1 i

end Saxl
namespace UniversalTensorSquare
open Saxl

theorem kronecker_pos_of_rowColumn_support {n : ℕ} {α μ : YoungDiagram}
    (hα : α.transpose = α) (a a' : Tableau n α) (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep t) (rowColumnCyclic a').toRepresentation)
    (hf : f ≠ 0) : 0 < kronecker a a t := by
  have hp := kronecker_pos_of_tensor_cyclic_support
    (transposeTableau a) (transposeTableau a') a a' t f hf
  obtain ⟨g,hg⟩ := (kronecker_pos_iff _ _ _).mp hp
  let E := spechtShapeEquiv hα (transposeTableau a) a
  let F := E.toIntertwiningMap.tensor (Representation.IntertwiningMap.id (spechtRep a))
  have hF : Function.Injective F :=
    (TensorProduct.congr E.toLinearEquiv (LinearEquiv.refl ℂ (Specht a))).injective
  apply (kronecker_pos_iff _ _ _).mpr
  refine ⟨F.comp g, ?_⟩
  intro hz
  apply hg
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have he := congrArg (fun H => H x) hz
  change F (g x) = 0 at he
  change F (g x) = F 0
  simpa only [map_zero] using he

lemma candidateHighLetter_marked (M b δ : ℕ) (hM : 4 ≤ M)
    (a : Fin ((staircase (M-2)).colLen 0)) :
    candidateMark M b (candidateHighLetter M b δ hM a).val := by
  have ha := a.isLt
  simp only [staircase_colLen, Nat.sub_zero] at ha
  dsimp [candidateMark, candidateHighLetter]
  split_ifs <;> omega

lemma candidateHighWord_alphabet (M b δ : ℕ) (hM : 4 ≤ M) :
    candidateHighWord M b δ hM ∈ alphabetSub _ _
      (fun a => candidateMark M b ((finProdFinEquiv.symm a).1).val) := by
  unfold candidateHighWord candidateHighMap staircaseWord
  rw [pairWordMap_tensor]
  apply pairWord_mem_alphabetLeft_gen (fun a => candidateMark M b a.val)
  apply letterLift_mem_alphabet
  intro a
  exact candidateHighLetter_marked M b δ hM a

lemma candidateBandRow_alphabet {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    candidateBandRow hM t ∈ alphabetSub _ _ (fun a => ¬ candidateMark M b a.val) := by
  apply altWord_mem_alphabet
  intro j
  have hn := candidateCutPositions_high t ((candidateCutPositions t).symm (Sum.inr j))
  simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, false_iff] at hn
  have hr := candidateRotateRow_mark M b δ hM (candidateBandTableau t j)
  have hh : ¬candidateMark M b (candidateRotateRow M b δ hM (candidateBandTableau t j)).val.2 :=
    fun hh => hn (hr.mp hh)
  simpa [rightWord, rowWord, transposeTableau, candidateRotateRowPositions, candidateBandTableau]
    using hh

lemma candidateBandWord_alphabet {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    candidateBandWord hM t ∈ alphabetSub _ _
      (fun a => ¬candidateMark M b ((finProdFinEquiv.symm a).1).val) := by
  exact pairWord_mem_alphabetLeft_gen (fun a => ¬candidateMark M b a.val) _ _
    (candidateBandRow_alphabet hM t)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SubdiagramSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdiagram Support. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma diagonalCut_mono (μ : YoungDiagram) : Monotone (diagonalCut μ) := by
  intro a b hab c hc
  have hc' := (mem_diagonalCut _ _ _).mp hc
  exact (mem_diagonalCut _ _ _).mpr ⟨hc'.1, hc'.2.trans_le hab⟩

lemma diagonalCut_exhausts (μ : YoungDiagram) : ∃ k, diagonalCut μ k = μ := by
  refine ⟨μ.cells.sup (fun c => c.1+c.2+1), ?_⟩
  apply SetLike.ext
  intro c
  simp only [mem_diagonalCut, and_iff_left_iff_imp]
  intro hc
  have h := Finset.le_sup (f := fun c : ℕ × ℕ => c.1+c.2+1) hc
  omega

lemma diagonalCut_strip (ν μ : YoungDiagram) (k : ℕ) :
    HorizontalStrip (ν ⊔ diagonalCut μ k) (ν ⊔ diagonalCut μ (k+1)) := by
  refine ⟨sup_le_sup_left (diagonalCut_mono μ (Nat.le_succ k)) ν, ?_⟩
  intro x hx hnx y hy hny hxy
  have hcut (c : ℕ × ℕ) (hc : c ∈ ν ⊔ diagonalCut μ (k+1))
      (hnc : c ∉ ν ⊔ diagonalCut μ k) : c.1+c.2 = k := by
    simp only [YoungDiagram.mem_sup, mem_diagonalCut] at hc hnc
    rcases hc with hc | hc
    · exact False.elim (hnc (Or.inl hc))
    · have hn : ¬ c.1+c.2 < k := fun hh => hnc (Or.inr ⟨hc.1,hh⟩)
      omega
  have hx' := hcut x hx hnx
  have hy' := hcut y hy hny
  apply Prod.ext <;> omega

theorem subdiagram_stripChain {ν μ : YoungDiagram} (h : ν ≤ μ) :
    ∃ bs : List ℕ, SizedStripChain bs ν μ := by
  have aux (k : ℕ) : ∃ bs : List ℕ, SizedStripChain bs ν (ν ⊔ diagonalCut μ k) := by
    induction k with
    | zero => exact ⟨[], by simpa using SizedStripChain.nil ν⟩
    | succ k ih =>
      obtain ⟨bs,hbs⟩ := ih
      have hs := diagonalCut_strip ν μ k
      have hc := Finset.card_le_card hs.1
      change (ν ⊔ diagonalCut μ k).card ≤ (ν ⊔ diagonalCut μ (k+1)).card at hc
      refine ⟨bs ++ [(ν ⊔ diagonalCut μ (k+1)).card-(ν ⊔ diagonalCut μ k).card], ?_⟩
      exact SizedStripChain.snoc hbs hs (by omega)
  obtain ⟨k,hk⟩ := diagonalCut_exhausts μ
  obtain ⟨bs,hbs⟩ := aux k
  exact ⟨bs, by simpa only [hk, sup_eq_right.mpr h] using hbs⟩

lemma positionProduct_swap {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d) :
    positionProduct (e.trans (Equiv.sumComm _ _)) u v = positionProduct e v u := by
  funext w
  change u (rightWord e w) * v (leftWord e w) = _
  exact mul_comm _ _

theorem subdiagram_product_support {n a b d : ℕ} {ν μ : YoungDiagram}
    (hνμ : ν ≤ μ) (s : Tableau b ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (fv : ∀ (η : YoungDiagram) (r : Tableau a η),
      ∃ F : Representation.IntertwiningMap (spechtRep r)
        (cyclic (wordRep a d) v).toRepresentation, F ≠ 0)
    (f : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep b d) u).toRepresentation) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, F ≠ 0 := by
  obtain ⟨bs,hbs⟩ := subdiagram_stripChain hνμ
  have hv' : v ∈ alphabetSub a d (fun z => ¬¬A z) := by simpa only [not_not] using hv
  have H := strip_product_support hbs s t (e.trans (Equiv.sumComm _ _)) u v
    (fun z => ¬A z) hu hv' f hf (fun η r _ => fv η r)
  rw [positionProduct_swap e v u] at H
  exact H

end Saxl
namespace UniversalTensorSquare
open Saxl

theorem candidate_subdiagram_support {n M b δ : ℕ} (hM : 4 ≤ M)
    (a : Tableau n (candidate M b δ)) {ν μ : YoungDiagram}
    (hνμ : ν ≤ μ) (r : Tableau (candidateBandSize a) ν) (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep r)
      (cyclic (wordRep _ _) (candidateBandWord hM a)).toRepresentation) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t) (rowColumnCyclic a).toRepresentation,
      F ≠ 0 := by
  have H := subdiagram_product_support hνμ r t (candidateCutPositions a)
    (candidateHighWord M b δ hM) (candidateBandWord hM a)
    (fun α => candidateMark M b ((finProdFinEquiv.symm α).1).val)
    (candidateHighWord_alphabet M b δ hM) (candidateBandWord_alphabet hM a)
    (candidateHighWord_support M b δ hM) f hf
  rw [← candidate_cut_factor hM a] at H
  obtain ⟨F,hF⟩ := H
  exact cyclic_projection_support (sameMarkProjection _ _ _ (candidateMark M b))
    (rowColumnWord a) F hF

theorem candidate_kronecker_pos_of_subdiagram_oai {n M b δ : ℕ} (hM : 4 ≤ M)
    (a : Tableau n (candidate M b δ)) {ν μ : YoungDiagram}
    (hνμ : ν ≤ μ) (r : Tableau (candidateBandSize a) ν) (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep r)
      (cyclic (wordRep _ _) (candidateBandWord hM a)).toRepresentation) (hf : f ≠ 0) :
    0 < kronecker a a t := by
  obtain ⟨F,hF⟩ := candidate_subdiagram_support hM a hνμ r t f hf
  exact kronecker_pos_of_rowColumn_support (candidate_transpose M b δ) a a t F hF

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.candidate_kronecker_pos_of_subdiagram_oai := @OAI.UniversalTensorSquare.candidate_kronecker_pos_of_subdiagram_oai
