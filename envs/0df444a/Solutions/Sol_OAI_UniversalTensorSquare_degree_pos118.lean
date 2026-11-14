-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos118
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T12:26:48.168201+00:00
-- url     : https://prove2.me/submissions/8a16d874-da16-4c0b-a798-1b3431a20906
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_Saxl_Balance_PackingPlan_realize
import Theorems.Thm_OAI_Saxl_Balance_short_pair_support
import Theorems.Thm_OAI_UniversalTensorSquare_band_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck118
import Theorems.Thm_OAI_UniversalTensorSquare_packingPlan_pos
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

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
-- module Solutions.OAIQ259_US.Saxl_SpechtDuality
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/

lemma subrepProject_pair {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule)
    (x : WordSpace n d) (y : S.toSubmodule) :
    dotProduct (subrepProject S hS x).val y.val = dotProduct x y.val := by
  have hh := (subrepSelfDual S hS).apply_symm_apply (subrepPairFromAmbient S x)
  exact congrArg (fun f : Module.Dual ℂ S.toSubmodule => f y) hh

/- A tensor power of a single letter-linear map, in ordinary word coordinates. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_HighProjection
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/


lemma columnAlt_left {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    wordRep n d (h : Equiv.Perm (Fin n)) * columnAlt (d := d) t =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((h * g : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((h * g : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  rw [← mul_assoc, signC_mul_self, one_mul]

lemma polytabloid_alternating {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) : wordRep n (μ.colLen 0) (h : Equiv.Perm (Fin n))
      (polytabloid t) = signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  rw [← columnAlt_row]
  exact congrArg (fun L : Module.End ℂ (WordSpace n (μ.colLen 0)) =>
    L (Pi.single (rowWord t) 1)) (columnAlt_left t h)

/- Move low row letters to the band and high row letters to B_h. -/

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

lemma cyclic_action_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (g : G) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic ρ v))
  · apply (cyclic_le _ _ _).mpr
    have hh := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic ρ (ρ g v))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at hh
    exact hh

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
-- module Solutions.OAIQ259_US.Saxl_SignEquivalence
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

lemma signTwist_irreducible {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (signTwist ρ) := by
  let cv : Subrepresentation (signTwist ρ) ≃o Subrepresentation ρ :=
    { toFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g x hx
            have h := S.toSubmodule.smul_mem (signC g) (S.apply_mem_toSubmodule g hx)
            change signC g • (signC g • (ρ g x)) ∈ S.toSubmodule at h
            simpa only [smul_smul, signC_mul_self, one_smul] using h }
      invFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g x hx
            exact S.toSubmodule.smul_mem (signC g) (S.apply_mem_toSubmodule g hx) }
      left_inv := by intro S; rfl
      right_inv := by intro S; rfl
      map_rel_iff' := by intros; rfl }
  exact cv.isSimpleOrder_iff.mpr inferInstance

lemma orbitAverage_base {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (a : Fin n → Fin d) (y : V)
    (hy : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ρ g y = y) :
    orbitAverage ρ a y (Pi.single a 1) =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin n) => a ∘ g = a)).card : ℂ) • y := by
  classical
  change (∑ g : Equiv.Perm (Fin n), (Pi.single a (1 : ℂ) : WordSpace n d) (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y) = _
  have hi (g : Equiv.Perm (Fin n)) : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a ↔ a ∘ g = a := by
    constructor <;> intro hh <;> funext i
    · have he := congrFun hh (g i); simpa using he.symm
    · have he := congrFun hh (g⁻¹ i); simpa using he.symm
  simp only [Pi.single_apply, hi]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_congr rfl (fun g hg => hy g (Finset.mem_filter.mp hg).2)]
  simp [Nat.cast_smul_eq_nsmul]

end Saxl

namespace Saxl
/- Sign-conjugacy proved using the column-antisymmetrized row tabloids. -/
theorem specht_sign_transpose {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Nonempty ((spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) := by
  classical
  let tt := transposeTableau t
  let y : Specht tt := ⟨polytabloid tt, mem_cyclic _ _⟩
  let R := signTwist (spechtRep tt)
  let F := orbitAverage R (rowWord t) y
  let c : ℂ := ((Finset.univ.filter
    (fun g : Equiv.Perm (Fin n) => rowWord t ∘ g = rowWord t)).card : ℂ)
  have hy : ∀ g : Equiv.Perm (Fin n), rowWord t ∘ g = rowWord t → R g y = y := by
    intro g hg
    have hc : g ∈ columnGroup tt := by
      intro i
      exact congrArg Fin.val (congrFun hg i)
    apply Subtype.ext
    change signC g • wordRep n (μ.transpose.colLen 0) g (polytabloid tt) = polytabloid tt
    rw [polytabloid_alternating tt ⟨g, hc⟩, smul_smul, signC_mul_self, one_smul]
  have hF : F (Pi.single (rowWord t) 1) = c • y := orbitAverage_base R _ y hy
  have hc0 : c ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply Finset.card_ne_zero.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rfl
  have hm (g : columnGroup t) :
      (F (wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n))
        (Pi.single (rowWord t) 1))).val (rowWord tt) = signC (g : Equiv.Perm (Fin n)) * c := by
    rw [F.isIntertwining, hF]
    change signC (g : Equiv.Perm (Fin n)) * (c *
      polytabloid tt (rowWord tt ∘ (g : Equiv.Perm (Fin n)))) = _
    have he : rowWord tt ∘ (g : Equiv.Perm (Fin n)) = rowWord tt := by
      funext i
      apply Fin.ext
      exact g.property i
    rw [he, polytabloid_rowWord, mul_one]
  let inc : Representation.IntertwiningMap (spechtRep t) (wordRep n (μ.colLen 0)) :=
    { toLinearMap := (spechtSub t).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let f := F.comp inc
  have hf : f ≠ 0 := by
    intro hz
    have he : (F (polytabloid t)).val (rowWord tt) = 0 := by
      have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) R =>
        (l ⟨polytabloid t, mem_cyclic _ _⟩).val (rowWord tt)) hz
      exact he
    let := Fintype.ofFinite (columnGroup t)
    have hp : (F (polytabloid t)).val (rowWord tt) =
        (Fintype.card (columnGroup t) : ℂ) * c := by
      change (F (∑ g : columnGroup t, signC (g : Equiv.Perm (Fin n)) •
        wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1))).val _ = _
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm]
      simp only [← mul_assoc, signC_mul_self, one_mul, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_ne_zero hn hc0) (hp.symm.trans he)
  let := specht_irreducible t
  let := specht_irreducible tt
  let := signTwist_irreducible (spechtRep tt)
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩
end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PieriRestriction
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A horizontal strip removes at most one cell in each column. -/

lemma wordRestrict_single {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (c : Fin n → Fin e) (b : Fin a → Fin d) :
    wordRestrict i j (Pi.single c 1) b = if c ∘ i = j ∘ b then 1 else 0 := by
  classical
  change (∑ z : Fin n → Fin e, if z ∘ i = j ∘ b then (Pi.single c (1 : ℂ) : WordSpace n e) z else 0) = _
  rw [Finset.sum_eq_single c]
  · simp
  · intro z hz hzc
    simp [hzc]
  · simp

lemma wordRestrict_equivariant {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)) (hi : ∀ k, g (i k) = i (h k))
    (x : WordSpace n e) :
    wordRestrict i j (wordRep n e g x) = wordRep a d h (wordRestrict i j x) := by
  classical
  ext b
  change (∑ c : Fin n → Fin e, if c ∘ i = j ∘ b then x (c ∘ g) else 0) =
    ∑ c : Fin n → Fin e, if c ∘ i = j ∘ (b ∘ h) then x c else 0
  apply Eq.trans ?_ (Equiv.sum_comp (wordPerm n e g)
    (fun c => if c ∘ i = j ∘ (b ∘ h) then x c else 0))
  apply Finset.sum_congr rfl
  intro c hc
  change (if c ∘ i = j ∘ b then x (c ∘ g) else 0) =
    if (c ∘ g) ∘ i = j ∘ (b ∘ h) then x (c ∘ g) else 0
  congr 1
  apply propext
  constructor
  · intro hh
    funext k
    simpa only [Function.comp_apply, hi] using congrFun hh (h k)
  · intro hh
    funext k
    have he := congrFun hh (h⁻¹ k)
    simpa [Function.comp_apply, hi] using he


lemma column_fixed_of_strip {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ)
    (g : columnGroup t) (hg : ∀ i, (g : Equiv.Perm (Fin n)) (tableauInclusion s t hs.1 i) =
      tableauInclusion s t hs.1 i) : g = 1 := by
  have hin (k : Fin n) (hk : (t k).val ∈ ν) : (g : Equiv.Perm (Fin n)) k = k := by
    let i := s.symm ⟨(t k).val, hk⟩
    have he : tableauInclusion s t hs.1 i = k := by
      apply t.injective
      apply Subtype.ext
      rw [tableauInclusion_cell]
      simp [i]
    simpa only [he] using hg i
  apply Subtype.ext
  apply Equiv.ext
  intro k
  by_cases hk : (t k).val ∈ ν
  · exact hin k hk
  · have ho : (t ((g : Equiv.Perm (Fin n)) k)).val ∉ ν := by
      intro hh
      have he := hin ((g : Equiv.Perm (Fin n)) k) hh
      have he' := (g : Equiv.Perm (Fin n)).injective he
      exact hk (he' ▸ hh)
    apply t.injective
    apply Subtype.ext
    exact hs.2 _ (t _).property ho _ (t _).property hk (g.property k)

lemma strip_contraction_coefficient {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
      (polytabloid t) (rowWord s) = 1 := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  have he (g : columnGroup t) :
      (rowWord t ∘ ((g : Equiv.Perm (Fin n))⁻¹ : Equiv.Perm (Fin n))) ∘ i = j ∘ rowWord s ↔ g = 1 := by
    constructor
    · intro hh
      have hf : ∀ k, ((g : Equiv.Perm (Fin n))⁻¹) (i k) = i k := by
        intro k
        apply t.injective
        apply Subtype.ext
        apply Prod.ext
        · have hh' := congrArg Fin.val (congrFun hh k)
          simpa [rowWord, j, rowLetterInclusion, i] using hh'
        · exact (g⁻¹).property (i k)
      have hh' : (g⁻¹ : columnGroup t) = 1 := column_fixed_of_strip s t hs (g⁻¹) hf
      simpa using congrArg Inv.inv hh'
    · rintro rfl
      funext k
      apply Fin.ext
      exact congrArg Prod.fst (tableauInclusion_cell s t hs.1 k)
  let := Fintype.ofFinite (columnGroup t)
  change wordRestrict i j (∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0)
      (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1)) (rowWord s) = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    wordRep_single, wordRestrict_single, he]
  simp

lemma column_viaEmbedding {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (g : columnGroup s) :
    (g : Equiv.Perm (Fin a)).viaEmbedding (tableauInclusion s t h) ∈ columnGroup t := by
  intro k
  by_cases hk : k ∈ Set.range (tableauInclusion s t h)
  · obtain ⟨l, rfl⟩ := hk
    rw [Equiv.Perm.viaEmbedding_apply]
    simpa only [tableauInclusion_cell] using g.property l
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk]

lemma signC_viaEmbedding {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin a)) :
    signC (g.viaEmbedding i) = signC g := by
  classical
  simp [signC_def, Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]

lemma strip_contraction_pair {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    dotProduct (wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
      (polytabloid t)) (polytabloid s) ≠ 0 := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  let x := wordRestrict i j (polytabloid t)
  have hx (g : columnGroup s) : wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a)) x =
      signC (g : Equiv.Perm (Fin a)) • x := by
    rw [← wordRestrict_equivariant i j ((g : Equiv.Perm (Fin a)).viaEmbedding i)
      (g : Equiv.Perm (Fin a)) (Equiv.Perm.viaEmbedding_apply _ _) (polytabloid t)]
    rw [polytabloid_alternating t ⟨_, column_viaEmbedding s t hs.1 g⟩]
    rw [map_smul, signC_viaEmbedding]
  rw [← columnAlt_coefficient]
  let := Fintype.ofFinite (columnGroup s)
  have he : columnAlt s x = (Fintype.card (columnGroup s) : ℂ) • x := by
    change (∑ g : columnGroup s, signC (g : Equiv.Perm (Fin a)) •
      wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a))) x = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul,
      signC_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  change columnAlt s x (rowWord s) ≠ 0
  rw [he]
  change (Fintype.card (columnGroup s) : ℂ) *
    wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1) (polytabloid t) (rowWord s) ≠ 0
  rw [strip_contraction_coefficient s t hs, mul_one]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/- Positive horizontal-strip Pieri map, equivariant for the full Young subgroup. -/
theorem pieri_strip_restriction {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, F ≠ 0 ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by
  let pr := subrepProject (spechtSub s) (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
  let T := wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
  let F := pr.toLinearMap.comp (T.comp (spechtSub t).toSubmodule.subtype)
  refine ⟨F, ?_, ?_⟩
  · intro hF
    have hp := subrepProject_pair (spechtSub s)
      (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
      (T (polytabloid t)) ⟨polytabloid s, mem_cyclic _ _⟩
    have he : pr (T (polytabloid t)) = 0 := by
      exact congrArg (fun L : Specht t →ₗ[ℂ] Specht s => L ⟨polytabloid t, mem_cyclic _ _⟩) hF
    rw [he] at hp
    exact strip_contraction_pair s t hs (hp.symm.trans (zero_dotProduct _))
  · intro g h hh x
    change pr (T (wordRep n (μ.colLen 0) g x.val)) = spechtRep s h (pr (T x.val))
    rw [wordRestrict_equivariant _ _ g h hh x.val]
    exact LinearMap.congr_fun (pr.isIntertwining' h) (T x.val)

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

lemma pieri_strip_surjective {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, Function.Surjective F ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by
  obtain ⟨F,hF,he⟩ := pieri_strip_restriction s t hs
  let E : Representation.IntertwiningMap
      ((spechtRep t).comp (Equiv.Perm.viaEmbeddingHom (tableauInclusion s t hs.1)))
      (spechtRep s) :=
    { toLinearMap := F
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro x
        exact he _ h (fun k => Equiv.Perm.viaEmbedding_apply _ _ k) x }
  have hE : E ≠ 0 := by
    intro hz
    exact hF (congrArg Representation.IntertwiningMap.toLinearMap hz)
  have := specht_irreducible s
  exact ⟨F, (Representation.IsIrreducible.surjective_or_eq_zero E).resolve_right hE, he⟩

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
    obtain ⟨F,hF,hFe⟩ := pieri_strip_surjective s t
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
    obtain ⟨P,hP,hPe⟩ := pieri_strip_surjective (shapeTableau η) t hh
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
-- module Solutions.OAIQ259_US.Saxl_HorizontalRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl


lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  simp [rowPrefix, Finset.sum_range_succ]

lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Separation. -/

section

noncomputable section
namespace Saxl

lemma equal_sets_of_card_sum_gap {X : Type*} [DecidableEq X]
    (A B : Finset X) (z : X → ℤ) (hc : A.card = B.card)
    (hz : ∑ x ∈ A, z x = ∑ x ∈ B, z x)
    (hgap : ∀ x ∈ A \ B, ∀ y ∈ B \ A, z y < z x) : A = B := by
  classical
  have he := Finset.card_sdiff_comm hc
  let e : ↥(A \ B) ≃ ↥(B \ A) := Finset.equivOfCardEq he
  have hsum : ∑ x ∈ A \ B, z x = ∑ x ∈ B \ A, z x := by
    have h₁ := Finset.sum_sdiff_eq_sub (f := z) (Finset.inter_subset_left (s₁ := A) (s₂ := B))
    have h₂ := Finset.sum_sdiff_eq_sub (f := z) (Finset.inter_subset_right (s₁ := A) (s₂ := B))
    simp only [Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right] at h₁ h₂
    rw [h₁, h₂, hz]
  have hn : A \ B = ∅ := by
    by_contra hn
    have hs : (Finset.univ : Finset ↥(A \ B)).Nonempty := by
      obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      exact ⟨⟨x,hx⟩,Finset.mem_univ _⟩
    have hh : (∑ x : ↥(A \ B), z (e x)) < ∑ x : ↥(A \ B), z x := by
      apply Finset.sum_lt_sum_of_nonempty hs
      intro x hx
      exact hgap x.val x.property (e x).val (e x).property
    rw [Equiv.sum_comp e (fun y : ↥(B \ A) => z y),
      Finset.sum_coe_sort, Finset.sum_coe_sort, hsum] at hh
    exact lt_irrefl _ hh
  exact Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp hn) hc.ge

theorem ordered_output_fibers_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (a b : X → ℕ) (z : X → ℤ)
    (ho : ∀ x ∈ s, ∀ y ∈ s, b x < b y → z x < z y)
    (hc : ∀ k, (s.filter (fun x => a x = k)).card =
      (s.filter (fun x => b x = k)).card)
    (hz : ∀ k, ∑ x ∈ s.filter (fun x => a x = k), z x =
      ∑ x ∈ s.filter (fun x => b x = k), z x) :
    ∀ k, s.filter (fun x => a x = k) = s.filter (fun x => b x = k) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    apply equal_sets_of_card_sum_gap _ _ z (hc k) (hz k)
    intro x hx y hy
    obtain ⟨hxA,hxB⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyB,hyA⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hxs,hxa⟩ := Finset.mem_filter.mp hxA
    obtain ⟨hys,hyb⟩ := Finset.mem_filter.mp hyB
    have hxne : b x ≠ k := by
      intro hh
      exact hxB (Finset.mem_filter.mpr ⟨hxs,hh⟩)
    have hxge : k ≤ b x := by
      by_contra hh
      have hh' : b x < k := Nat.lt_of_not_ge hh
      have hi := ih (b x) hh'
      have hx' : x ∈ s.filter (fun w => a w = b x) := by
        rw [hi]
        exact Finset.mem_filter.mpr ⟨hxs,rfl⟩
      have ha := (Finset.mem_filter.mp hx').2
      omega
    exact ho y hys x hxs (by omega)

lemma ordered_output_labels_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (a b : X → ℕ) (z : X → ℤ)
    (ho : ∀ x ∈ s, ∀ y ∈ s, b x < b y → z x < z y)
    (hc : ∀ k, (s.filter (fun x => a x = k)).card =
      (s.filter (fun x => b x = k)).card)
    (hz : ∀ k, ∑ x ∈ s.filter (fun x => a x = k), z x =
      ∑ x ∈ s.filter (fun x => b x = k), z x) :
    ∀ x ∈ s, a x = b x := by
  intro x hx
  have he := ordered_output_fibers_eq s a b z ho hc hz (b x)
  have hh : x ∈ s.filter (fun w => a w = b x) := by
    rw [he]
    exact Finset.mem_filter.mpr ⟨hx,rfl⟩
  exact (Finset.mem_filter.mp hh).2

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OneExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One Extra. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma intertwining_comp_ne_zero {G X Y Z : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap σ τ) (hF : Function.Injective F)
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) : F.comp f ≠ 0 := by
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have hh := congrArg (fun H => H x) hz
  exact hh.trans (map_zero F).symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Projection. -/

section

noncomputable section
namespace Saxl.Balance

lemma balanceWords_iff_components {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (w : Fin n → Fin d)
    (hw : ∀ k, ∑ i ∈ Finset.univ.filter (fun i => c i = k), z (w i) = σ k) :
    balanceWords c A label z σ w ↔ componentWords c A label w := by
  classical
  constructor
  · rintro ⟨hA,hcs⟩
    refine ⟨hA,fun i => ?_⟩
    exact (ordered_output_labels_eq Finset.univ c (fun i => label (w i))
      (fun i => z (w i)) (fun i hi j hj hh => ho _ _ (hA i) (hA j) hh)
      (fun k => (hcs k).1.symm) (fun k => (hw k).trans (hcs k).2.symm)
      i (Finset.mem_univ i)).symm
  · rintro ⟨hA,hl⟩
    refine ⟨hA, fun k => ?_⟩
    simp only [hl]
    exact ⟨True.intro,hw k⟩

theorem balance_projection_eq {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (x : WordSpace n d) (hx : FixedComponentSums c z σ x) :
    coordinateProjection (balanceWords c A label z σ) x =
      coordinateProjection (componentWords c A label) x := by
  classical
  funext w
  by_cases hw : x w = 0
  · simp only [coordinateProjection_apply, hw, ite_self]
  · simp only [coordinateProjection_apply,
      balanceWords_iff_components c A label z σ ho w (hx w hw)]

theorem component_projection_mem {n d : ℕ} (c : Fin n → ℕ) (A : Fin d → Prop)
    (label : Fin d → ℕ) (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (W : Subrepresentation (wordRep n d)) (x : WordSpace n d)
    (hxW : x ∈ W) (hx : FixedComponentSums c z σ x) :
    coordinateProjection (componentWords c A label) x ∈
      ((invariantCoordinateProjection (balanceWords c A label z σ)
        (balanceWords_invariant c A label z σ)).comp (subrepInclusion W)).range := by
  refine ⟨⟨x,hxW⟩, ?_⟩
  exact balance_projection_eq c A label z σ ho x hx

theorem components_support_transfer {n d : ℕ} {X : Type*}
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (f : X →ₗ[ℂ] WordSpace n d) (hf : f ≠ 0)
    (he : ∀ g ∈ fiberGroup c, ∀ x, f (ρ g x) = wordRep n d g (f x))
    (hm : ∀ x, f x ∈ W)
    (hs : ∀ x w, f x w ≠ 0 → componentWords c A label w) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  classical
  let P := coordinateProjection (componentWords c A label)
  have hP (x) : P (f x) = f x := by
    ext w
    change (if componentWords c A label w then f x w else 0) = _
    split_ifs with h
    · rfl
    · exact (not_ne_iff.mp (fun hh => h (hs x w hh))).symm
  have hk (g : Equiv.Perm (Fin n)) (hg : g ∉ fiberGroup c) (x) :
      P (wordRep n d g (f x)) = 0 := by
    ext w
    change (if componentWords c A label w then f x (w ∘ g) else 0) = 0
    split_ifs with hw
    · by_contra hn
      have hh := hs x (w ∘ g) hn
      apply hg
      intro i
      exact (hw.2 (g i)).symm.trans (hh.2 i)
    · rfl
  let F := averagedMap ρ (wordRep n d) f
  have hF : F ≠ 0 := sector_average_nonzero ρ (wordRep n d) (fiberGroup c) f hf he P hP hk
  have hmem (x) : F x ∈ W := by
    rw [show F x = _ from averagedMap_apply ρ (wordRep n d) f x]
    apply Submodule.sum_mem
    intro g hg
    exact W.apply_mem_toSubmodule g (hm _)
  let T : Representation.IntertwiningMap ρ W.toRepresentation :=
    { toLinearMap := F.toLinearMap.codRestrict _ hmem
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact LinearMap.congr_fun (F.isIntertwining' g) x }
  refine ⟨T, ?_⟩
  intro hz
  apply hF
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun l => l x) hz)

theorem balance_support_transfer {n d : ℕ} {X : Type*}
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (L : X →ₗ[ℂ] WordSpace n d)
    (hm : ∀ x, L x ∈ W) (hσ : ∀ x, FixedComponentSums c z σ (L x))
    (hf : (coordinateProjection (componentWords c A label)).comp L ≠ 0)
    (he : ∀ g ∈ fiberGroup c, ∀ x,
      coordinateProjection (componentWords c A label) (L (ρ g x)) =
      wordRep n d g (coordinateProjection (componentWords c A label) (L x))) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  classical
  let P := (invariantCoordinateProjection (balanceWords c A label z σ)
    (balanceWords_invariant c A label z σ)).comp (subrepInclusion W)
  let f := (coordinateProjection (componentWords c A label)).comp L
  have hmem (x) : f x ∈ P.range :=
    component_projection_mem c A label z σ ho W (L x) (hm x) (hσ x)
  have hsector (x w) (hw : f x w ≠ 0) : componentWords c A label w := by
    by_contra hn
    exact hw (by change (if componentWords c A label w then L x w else 0) = 0; rw [ite_eq_right hn])
  obtain ⟨T,hT⟩ := components_support_transfer ρ P.range c A label f hf he hmem hsector
  obtain ⟨i,hi⟩ := subrepresentation_embeds_of_le_range P P.range le_rfl
  refine ⟨i.comp T, ?_⟩
  exact intertwining_comp_ne_zero i hi T hT

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SupportTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support Transport. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

namespace SupportLE
variable {G H X Y Z : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    [AddCommMonoid Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}

lemma refl (ρ : Representation ℂ G X) : SupportLE ρ ρ := by
  intro x hx
  exact ⟨Representation.IntertwiningMap.id ρ, hx⟩

lemma detects_map {W : Type*} [AddCommMonoid W] [Module ℂ W]
    {υ : Representation ℂ G W} (h : SupportLE ρ σ)
    (f : Representation.IntertwiningMap υ ρ) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap υ σ, g ≠ 0 := by
  have hn : ∃ x, f x ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext hh))
  obtain ⟨x,hx⟩ := hn
  obtain ⟨g,hg⟩ := h (f x) hx
  exact ⟨g.comp f,fun hz => hg (congrArg (fun F : Representation.IntertwiningMap υ σ => F x) hz)⟩

end SupportLE

end Saxl

namespace Saxl

lemma coindEval_ne_zero {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap ρ (Representation.coind φ σ)) (hf : f ≠ 0) :
    coindEval φ f ≠ 0 := by
  intro hz
  apply hf
  rw [← coindLift_eval φ f,hz]
  ext x g
  rfl

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

theorem balance_support_of_surjective {n d : ℕ} {G X Y : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (φ : G →* fiberGroup c) (hφ : Function.Surjective φ)
    (τ : Representation ℂ G Y)
    (L : Y →ₗ[ℂ] WordSpace n d)
    (hm : ∀ y, L y ∈ W) (hs : ∀ y, FixedComponentSums c z σ (L y))
    (T : Representation.IntertwiningMap τ
      ((wordRep n d).comp ((fiberGroup c).subtype.comp φ)))
    (hT : Function.Injective T)
    (he : ∀ y, coordinateProjection (componentWords c A label) (L y) = T y)
    (f : Representation.IntertwiningMap
      (ρ.comp ((fiberGroup c).subtype.comp φ)) τ) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  let K := L.comp f.toLinearMap
  have hK : (coordinateProjection (componentWords c A label)).comp K ≠ 0 := by
    intro h0
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply hT
    change T (f x) = T 0
    rw [map_zero, ← he]
    exact LinearMap.congr_fun h0 x
  apply balance_support_transfer ρ W c A label z σ ho K
    (fun x => hm (f x)) (fun x => hs (f x)) hK
  intro g hg x
  obtain ⟨a,ha⟩ := hφ ⟨g,hg⟩
  have hval : (φ a).val = g := congrArg Subtype.val ha
  change coordinateProjection (componentWords c A label) (L (f (ρ g x))) =
    wordRep n d g (coordinateProjection (componentWords c A label) (L (f x)))
  rw [he,he,← hval]
  exact LinearMap.congr_fun ((T.comp f).isIntertwining' a) x

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Gluing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

theorem Piece.support {n d : ℕ} {G X Y : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {v : WordSpace n d} {c : Fin n → ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {σ : ℕ → ℤ}
    {φ : G →* fiberGroup c} {τ : Representation ℂ G Y}
    (P : Piece v c A label σ φ τ)
    (ho : ∀ a b, A a → A b → label a < label b → output a < output b)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (F : Representation.IntertwiningMap ρ (Representation.coind ((fiberGroup c).subtype.comp φ) τ))
    (hF : F ≠ 0) :
    ∃ T : Representation.IntertwiningMap ρ (cyclicSquareMap v).range.toRepresentation, T ≠ 0 := by
  exact balance_support_of_surjective ρ (cyclicSquareMap v).range c A label
    (fun a => (output a : ℤ)) σ (by intro a b ha hb hl; exact_mod_cast ho a b ha hb hl)
    φ P.surj τ P.raw P.raw_mem P.raw_sums P.projected P.injective P.projection_eq
    (coindEval ((fiberGroup c).subtype.comp φ) F)
    (coindEval_ne_zero ((fiberGroup c).subtype.comp φ) F hF)

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ZeroColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

lemma sum_fin_val_ite (r i : ℕ) :
    (∑ j : Fin r, if j.val = i then (1:ℕ) else 0) = if i < r then 1 else 0 := by
  classical
  by_cases hi : i < r
  · rw [ite_eq_left hi, Finset.sum_eq_single (⟨i,hi⟩ : Fin r)]
    · simp
    · intro j hj hji
      exact ite_eq_right (fun h => hji (Fin.ext h))
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h : (j : ℕ) = i => hi (h ▸ j.isLt))

lemma cells_row_count (rs : List ℕ) (i : ℕ) :
    (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) = rs.countP (fun h => i < h) := by
  classical
  induction rs with
  | nil => simp [Cells]
  | cons h rs ih =>
    rw [show (∑ c : Cells (h :: rs), if row c = i then (1:ℕ) else 0) =
      (∑ c : Fin h, if c.val = i then (1:ℕ) else 0) +
        (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) from
      Fintype.sum_sum_type _]
    rw [sum_fin_val_ite, ih, List.countP_cons]
    split_ifs <;> simp_all <;> omega

lemma placed_rowLen {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (i : ℕ) :
    μ.rowLen i = rs.countP (fun h => i < h) := by
  classical
  let E : {c : Cells rs // row c = i} ≃ {c : μ.cells // c.val.1 = i} :=
    e.subtypeEquiv (fun c => by rw [hr])
  have hc := Fintype.card_congr (E.trans (rowFiberEquiv μ i))
  rw [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter, cells_row_count] at hc
  exact hc.symm

lemma columnShape_rowLen (rs : List ℕ) (i : ℕ) :
    (columnShape rs).rowLen i = rs.countP (fun h => i < h) := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_rowLen e hr i

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_TransposeSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transpose Support. -/

section

noncomputable section
open scoped TensorProduct

namespace UniversalTensorSquare

lemma canonical_sign_transpose {n : ℕ} (μ : YoungDiagram) (hμ : μ.card = n) :
    Nonempty ((Saxl.spechtRep (Saxl.canonicalTableau μ hμ)).Equiv
      (Saxl.signTwist (Saxl.spechtRep
        (Saxl.canonicalTableau μ.transpose ((Saxl.transpose_card μ).trans hμ))))) := by
  obtain ⟨e⟩ := Saxl.specht_sign_transpose (Saxl.canonicalTableau μ hμ)
  let e' := Saxl.equivOfSubrepEq
    (Saxl.spechtSub (Saxl.transposeTableau (Saxl.canonicalTableau μ hμ)))
    (Saxl.spechtSub
      (Saxl.canonicalTableau μ.transpose ((Saxl.transpose_card μ).trans hμ)))
    (Saxl.spechtSub_tableau_independent _ _)
  exact ⟨e.trans (signTwistEquiv e')⟩

lemma canonical_self_sign {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) :
    Nonempty ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).Equiv
      (Saxl.signTwist (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)))) := by
  obtain ⟨e⟩ := canonical_sign_transpose lam hlam
  let e' := spechtShapeEquiv hself
    (Saxl.canonicalTableau lam.transpose ((Saxl.transpose_card lam).trans hlam))
    (Saxl.canonicalTableau lam hlam)
  exact ⟨e.trans (signTwistEquiv e')⟩

lemma tensorAnti_injective {n : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin n)) Z}
    (e : σ.Equiv (Saxl.signTwist τ)) :
    Function.Injective (Saxl.tensorAnti ρ e.toIntertwiningMap) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ X) e.toLinearEquiv).injective

lemma kronecker_pos_transpose {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n)
    (hpos : 0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) :
    0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν)) := by
  obtain ⟨eL⟩ := canonical_self_sign lam hlam hself
  obtain ⟨eν⟩ := canonical_sign_transpose ν hν
  obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp hpos
  let A := Saxl.tensorAnti (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))
    eL.toIntertwiningMap
  let B := (Saxl.signTwistMap
    (Y := Saxl.Specht (Saxl.canonicalTableau lam hlam) ⊗[ℂ]
      Saxl.Specht (Saxl.canonicalTableau lam hlam)) f).comp (Saxl.signCancelMap eν.symm.toIntertwiningMap)
  apply (Saxl.kronecker_pos_iff _ _ _).mpr
  refine ⟨A.comp B, ?_⟩
  intro hz
  apply hf
  ext x
  have h := congrArg (fun F => F (eν x)) hz
  have hi : Function.Injective A := tensorAnti_injective _ eL
  apply hi
  change A (f x) = A 0
  change A (f (eν.symm (eν x))) = 0 at h
  simpa only [eν.symm_apply_apply, map_zero] using h

theorem kronecker_pos_transpose_iff {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n) :
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ↔
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν))) := by
  constructor
  · exact kronecker_pos_transpose lam hlam hself ν hν
  · intro h
    have ht := kronecker_pos_transpose lam hlam hself ν.transpose
      ((Saxl.transpose_card ν).trans hν) h
    obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp ht
    let e := spechtShapeEquiv (YoungDiagram.transpose_transpose ν).symm
      (Saxl.canonicalTableau ν hν)
      (Saxl.canonicalTableau ν.transpose.transpose
        ((Saxl.transpose_card ν.transpose).trans ((Saxl.transpose_card ν).trans hν)))
    apply (Saxl.kronecker_pos_iff _ _ _).mpr
    refine ⟨f.comp e.toIntertwiningMap, ?_⟩
    intro hz
    apply hf
    ext x
    have hh := congrArg (fun F => F (e.symm x)) hz
    change f (e (e.symm x)) = 0 at hh
    simpa using hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Strip. -/

section

noncomputable section

namespace Saxl.Balance

lemma horizontal_of_interlacing (ν μ : YoungDiagram)
    (hsub : ∀ i, ν.rowLen i ≤ μ.rowLen i)
    (hbtw : ∀ i, μ.rowLen (i+1) ≤ ν.rowLen i) : HorizontalStrip ν μ := by
  constructor
  · intro x hx
    exact YoungDiagram.mem_iff_lt_rowLen.mpr
      ((YoungDiagram.mem_iff_lt_rowLen.mp hx).trans_le (hsub x.1))
  · intro x hx hxν y hy hyν hxy
    apply Prod.ext _ hxy
    have hh : ∀ (p q : ℕ × ℕ), p ∈ μ → p ∉ ν → q ∈ μ → q ∉ ν →
        p.2 = q.2 → ¬ p.1 < q.1 := by
      intro p q _ hp hq _ hpq hlt
      have hp' := mt YoungDiagram.mem_iff_lt_rowLen.mpr hp
      have hq' := YoungDiagram.mem_iff_lt_rowLen.mp hq
      have hb := (μ.rowLen_anti _ _ (show p.1+1 ≤ q.1 by omega)).trans (hbtw p.1)
      omega
    exact Nat.le_antisymm (Nat.le_of_not_gt (hh y x hy hyν hx hxν hxy.symm))
      (Nat.le_of_not_gt (hh x y hx hxν hy hyν hxy))

lemma ofRowLens_height (A : List ℕ) (hA : A.SortedGE) :
    (YoungDiagram.ofRowLens A hA).colLen 0 ≤ A.length := by
  by_contra hh
  have h := YoungDiagram.mem_iff_lt_colLen.mpr
    (show A.length < (YoungDiagram.ofRowLens A hA).colLen 0 by omega)
  obtain ⟨h',_⟩ := YoungDiagram.mem_ofRowLens.mp h
  exact (Nat.lt_irrefl _) h'

lemma ofRowLens_rowLen (A : List ℕ) (hA : A.SortedGE) (i : ℕ) :
    (YoungDiagram.ofRowLens A hA).rowLen i = A[i]?.getD 0 := by
  by_cases hi : i < A.length
  · simpa [hi] using YoungDiagram.rowLen_ofRowLens (hw := hA) ⟨i,hi⟩
  · rw [rowLen_zero_of_height_le _ ((ofRowLens_height A hA).trans (by omega))]
    simp [List.getElem?_eq_none (by omega : A.length ≤ i)]

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPackingPieri
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing Pieri. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance
open FlagColumns Columns

lemma short_transpose_height (r δ : ℕ) : (ShortColumns.shape r δ).transpose.colLen 0 = r+δ := by
  rw [YoungDiagram.colLen_transpose]
  exact YoungDiagram.rowLen_ofRowLens (hw := by apply List.Pairwise.sortedGE; simp)
    (show Fin [r+δ,r].length from ⟨0,by simp⟩)

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OutputBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Output Bands. -/

section

noncomputable section
namespace Saxl.Balance

lemma OutputBands.label_spec (B : OutputBands) {x : ℕ} (h : B.Allows x) :
    B.label x ∈ B.starts ∧ B.label x ≤ x ∧ x ≤ B.upper (B.label x) := by
  rw [OutputBands.label,dite_eq_left h]
  exact Classical.choose_spec h

lemma OutputBands.unique (B : OutputBands) {x k l : ℕ}
    (hk : k ∈ B.starts) (hl : l ∈ B.starts)
    (hkx : k ≤ x) (hxk : x ≤ B.upper k) (hlx : l ≤ x) (hxl : x ≤ B.upper l) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · have := B.separated k hk l hl h
    omega
  · exact h
  · have := B.separated l hl k hk h
    omega

lemma OutputBands.label_iff (B : OutputBands) {k x : ℕ} (hk : k ∈ B.starts) :
    (B.Allows x ∧ B.label x = k) ↔ x ∈ Set.Icc k (B.upper k) := by
  constructor
  · rintro ⟨hx,hk'⟩
    have h := B.label_spec hx
    rw [hk'] at h
    exact h.2
  · rintro ⟨hkx,hxk⟩
    have hx : B.Allows x := ⟨k,hk,hkx,hxk⟩
    have h := B.label_spec hx
    exact ⟨hx,B.unique h.1 hk h.2.1 h.2.2 hkx hxk⟩

lemma OutputBands.ordered (B : OutputBands) {x y : ℕ}
    (hx : B.Allows x) (hy : B.Allows y) (hxy : B.label x < B.label y) : x < y := by
  have hx' := B.label_spec hx
  have hy' := B.label_spec hy
  exact lt_of_le_of_lt hx'.2.2 ((B.separated _ hx'.1 _ hy'.1 hxy).trans_le hy'.2.1)

lemma OutputBands.letter_iff (B : OutputBands) {d k : ℕ} (hk : k ∈ B.starts)
    (a : Fin (d*d)) :
    (B.alphabet d a ∧ B.letterLabel d a = k) ↔ output a ∈ Set.Icc k (B.upper k) :=
  B.label_iff hk

lemma OutputBands.letter_ordered (B : OutputBands) (d : ℕ) :
    ∀ x y, B.alphabet d x → B.alphabet d y →
      B.letterLabel d x < B.letterLabel d y → output x < output y := by
  intro x y hx hy h
  exact B.ordered hx hy h

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Capacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capacity. -/

section

noncomputable section

namespace UniversalTensorSquare

open Saxl

lemma colPrefix_eq_sum (μ : YoungDiagram) (i : ℕ) :
    colPrefix μ i = ∑ k ∈ Finset.range i, μ.colLen k := by
  simp only [colPrefix, rowPrefix, YoungDiagram.rowLen_transpose]

lemma mem_colTruncate (μ : YoungDiagram) (i : ℕ) (a b : ℕ) :
    (a,b) ∈ colTruncate μ i ↔ (a,b) ∈ μ ∧ b < i := by
  simp only [colTruncate, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    Saxl.mem_rowTruncate]

lemma rowTruncate_subset (μ : YoungDiagram) (j : ℕ) :
    (rowTruncate μ j).cells ⊆ μ.cells := by
  intro p hp
  exact (Saxl.mem_rowTruncate.mp hp).1

lemma colTruncate_subset (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).cells ⊆ μ.cells := by
  rintro ⟨a,b⟩ hp
  exact ((mem_colTruncate μ i a b).mp hp).1

lemma colTruncate_card (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).card = colPrefix μ i := by
  rw [colTruncate, Saxl.transpose_card, rowTruncate_card, colPrefix]

lemma strip_area_identity (μ : YoungDiagram) (i j : ℕ) :
    μ.card + ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card =
      rowPrefix μ j + colPrefix μ i +
        (μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells)).card := by
  have hu : (rowTruncate μ j).cells ∪ (colTruncate μ i).cells ⊆ μ.cells :=
    Finset.union_subset (rowTruncate_subset μ j) (colTruncate_subset μ i)
  have h₁ := Finset.card_sdiff_add_card_eq_card hu
  have h₂ := Finset.card_union_add_card_inter
    (rowTruncate μ j).cells (colTruncate μ i).cells
  have h₃ := rowTruncate_card μ j
  have h₄ := colTruncate_card μ i
  change (rowTruncate μ j).cells.card = _ at h₃
  change (colTruncate μ i).cells.card = _ at h₄
  change μ.cells.card + _ = _
  omega

lemma corner_subset_rectangle (μ : YoungDiagram) {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) ⊆
      Finset.Ico j (μ.colLen (i-1)) ×ˢ Finset.Ico i (μ.rowLen (j-1)) := by
  rintro ⟨a,b⟩ hp
  simp only [Finset.mem_sdiff, Finset.mem_union, YoungDiagram.mem_cells,
    mem_rowTruncate, mem_colTruncate, not_or] at hp
  have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1, ha⟩
  have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1, hb⟩
  have ha' : a < μ.colLen (i-1) := YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (by omega) hp.1)
  have hb' : b < μ.rowLen (j-1) := YoungDiagram.mem_iff_lt_rowLen.mp
    (μ.up_left_mem (by omega) le_rfl hp.1)
  simpa only [Finset.mem_product, Finset.mem_Ico] using And.intro ⟨ha, ha'⟩ ⟨hb,hb'⟩

lemma prefix_last_mul_le (μ : YoungDiagram) {j : ℕ} (hj : 0 < j) :
    j * μ.rowLen (j-1) ≤ rowPrefix μ j := by
  have h := Finset.sum_le_sum (s := Finset.range j) (f := fun _ => μ.rowLen (j-1))
    (g := fun a => μ.rowLen a) (by
      intro a ha
      exact μ.rowLen_anti a (j-1) (by have := Finset.mem_range.mp ha; omega))
  simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, rowPrefix] using h

lemma capacity_floor_bound (x f : ℕ) : x ≤ 2*((x-f)/2)+f+1 := by omega

lemma prefix_le_capacity (μ : YoungDiagram) (d q : ℕ) :
    colPrefix μ q ≤ 2*bandCapacity μ d q + q*(d+1) := by
  rw [colPrefix_eq_sum, bandCapacity]
  have h := Finset.sum_le_sum (s := Finset.range q)
    (fun k _ => capacity_floor_bound (μ.colLen k) d)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_add, Nat.mul_one,
    Nat.add_assoc] using h

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Intermediate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intermediate. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma first_prefix_height (μ : YoungDiagram) {K : ℕ} (hK : 0 < K)
    (h : K ≤ rowPrefix μ 4) :
    ∃ d, 1 ≤ d ∧ d ≤ 4 ∧ K ≤ rowPrefix μ d ∧
      (1 < d → rowPrefix μ (d-1) < K) := by
  let h' : ∃ d, K ≤ rowPrefix μ d := ⟨4,h⟩
  refine ⟨Nat.find h', ?_, Nat.find_min' h' h, Nat.find_spec h', ?_⟩
  · have hx := Nat.find_spec h'
    by_contra hh
    have hd : Nat.find h' = 0 := by omega
    change K ≤ rowPrefix μ (Nat.find h') at hx
    rw [hd] at hx
    simp only [rowPrefix, Finset.range_zero, Finset.sum_empty] at hx
    omega
  · intro hd
    exact Nat.lt_of_not_ge (Nat.find_min h' (by omega))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Capacity. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma prefix_last_after_first (μ : YoungDiagram) {j : ℕ} (hj : 0 < j) :
    μ.rowLen 0 + (j-1)*μ.rowLen (j-1) ≤ rowPrefix μ j := by
  have he : j = (j-1)+1 := by omega
  unfold rowPrefix
  conv_rhs => rw [he, Finset.sum_range_succ']
  have hh := Finset.sum_le_sum (s := Finset.range (j-1))
    (f := fun _ => μ.rowLen (j-1)) (g := fun a => μ.rowLen (a+1)) (by
      intro a ha
      exact μ.rowLen_anti _ _ (by have := Finset.mem_range.mp ha; omega))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hh
  omega

lemma endpointBound_sound (μ : YoungDiagram) {i U H : ℕ} (hi : 0 < i)
    (hU : rowPrefix μ i ≤ U) (hH : H ≤ μ.rowLen 0) :
    μ.rowLen (i-1) ≤ endpointBound i U H := by
  unfold endpointBound
  split_ifs with he
  · subst i
    simpa [rowPrefix] using hU
  · apply le_min
    · apply (Nat.le_div_iff_mul_le hi).mpr
      simpa [Nat.mul_comm] using (prefix_last_mul_le μ hi).trans hU
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < i-1)).mpr
      have h := prefix_last_after_first μ hi
      have hx : (i-1)*μ.rowLen (i-1) ≤ U-H := by omega
      simpa [Nat.mul_comm] using hx

lemma prefix_intersection_hook (μ : YoungDiagram) {i j H W : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hH : H ≤ μ.colLen 0) (hW : W ≤ μ.rowLen 0)
    (hHp : 0 < H) (hWp : 0 < W) :
    min i W + min j H - 1 ≤
      ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card := by
  let A := (rectangle 1 (min i W)).cells
  let B := (rectangle (min j H) 1).cells
  have hA : A ⊆ (rowTruncate μ j).cells ∩ (colTruncate μ i).cells := by
    rintro ⟨a,b⟩ hp
    have hx : a < 1 ∧ b < min i W := mem_rectangle.mp hp
    have ha : a = 0 := by omega
    subst a
    have hc : (0,b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    simpa only [Finset.mem_inter,YoungDiagram.mem_cells,mem_rowTruncate,mem_colTruncate]
      using And.intro ⟨hc,hj⟩ ⟨hc,lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have hB : B ⊆ (rowTruncate μ j).cells ∩ (colTruncate μ i).cells := by
    rintro ⟨a,b⟩ hp
    have hx : a < min j H ∧ b < 1 := mem_rectangle.mp hp
    have hb : b = 0 := by omega
    subst b
    have hc : (a,0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    simpa only [Finset.mem_inter,YoungDiagram.mem_cells,mem_rowTruncate,mem_colTruncate]
      using And.intro ⟨hc,lt_of_lt_of_le hx.1 (min_le_left _ _)⟩ ⟨hc,hi⟩
  have hAB : A ∩ B = {(0,0)} := by
    ext ⟨a,b⟩
    simp only [Finset.mem_inter,Finset.mem_singleton,Prod.mk.injEq]
    simp only [A,B,rectangle,Finset.mem_product,Finset.mem_range]
    omega
  have he := Finset.card_union_add_card_inter A B
  have ha : A.card = min i W := by simp [A,rectangle]
  have hb : B.card = min j H := by simp [B,rectangle]
  rw [hAB,Finset.card_singleton,ha,hb] at he
  have h := Finset.card_le_card (Finset.union_subset hA hB)
  omega

lemma area_le_refined (μ : YoungDiagram) {i j U V X Y H W : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hU : colPrefix μ i ≤ U) (hV : rowPrefix μ j ≤ V)
    (hX : μ.colLen (i-1) ≤ X) (hY : μ.rowLen (j-1) ≤ Y)
    (hH : H ≤ μ.colLen 0) (hW : W ≤ μ.rowLen 0) (hHp : 0 < H) (hWp : 0 < W) :
    μ.card ≤ refinedArea i j U V X Y H W := by
  classical
  have hid := strip_area_identity μ i j
  have hh := prefix_intersection_hook μ hi hj hH hW hHp hWp
  by_cases hcell : (j-1,i-1) ∈ μ
  · have heq : (rowTruncate μ j).cells ∩ (colTruncate μ i).cells =
        (rectangle j i).cells := by
      ext ⟨a,b⟩
      simp only [Finset.mem_inter, YoungDiagram.mem_cells, mem_rowTruncate,
        mem_colTruncate, mem_rectangle]
      constructor
      · tauto
      · rintro ⟨ha,hb⟩
        have hx := μ.up_left_mem (by omega : a ≤ j-1) (by omega : b ≤ i-1) hcell
        tauto
    have hint : ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card = j*i := by
      rw [heq]
      simp only [rectangle,Finset.card_product,Finset.card_range]
    have hcor := Finset.card_le_card (corner_subset_rectangle μ hi hj)
    simp only [Finset.card_product,Nat.card_Ico] at hcor
    have hmul := Nat.mul_le_mul (Nat.sub_le_sub_right hX j) (Nat.sub_le_sub_right hY i)
    have hx : j ≤ μ.colLen (i-1) := by
      have := YoungDiagram.mem_iff_lt_colLen.mp hcell; omega
    have hy : i ≤ μ.rowLen (j-1) := by
      have := YoungDiagram.mem_iff_lt_rowLen.mp hcell; omega
    rw [hint] at hid
    have hup : i*j ≤ U+V := by
      have ht := prefix_last_mul_le μ.transpose hi
      simp only [YoungDiagram.rowLen_transpose] at ht
      change i * μ.colLen (i-1) ≤ colPrefix μ i at ht
      nlinarith
    have hsub := Nat.sub_add_cancel hup
    have ha : μ.card ≤ U+V-i*j+(X-j)*(Y-i) := by
      rw [Nat.mul_comm j i] at hid
      omega
    unfold refinedArea
    rw [ite_eq_left ⟨hx.trans hX,hy.trans hY⟩]
    exact ha.trans (le_max_right _ _)
  · have hz : μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨a,b⟩ hp
      simp only [Finset.mem_sdiff,Finset.mem_union,YoungDiagram.mem_cells,
        mem_rowTruncate,mem_colTruncate,not_or] at hp
      have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1,ha⟩
      have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1,hb⟩
      exact hcell (μ.up_left_mem (by omega) (by omega) hp.1)
    rw [hz,Finset.card_empty,add_zero] at hid
    have ha : μ.card ≤ U+V-(min i W+min j H-1) := by omega
    unfold refinedArea
    split_ifs
    · exact ha.trans (le_max_left _ _)
    · exact ha

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma minHeight_pos (n : ℕ) (B : List (ℕ × ℕ)) : 0 < minHeight n B := by
  induction B with
  | nil => simp [minHeight]
  | cons p B ih =>
    simp only [minHeight,List.foldr_cons]
    split_ifs
    · exact lt_of_lt_of_le ih (le_max_right _ _)
    · exact ih

lemma minHeight_sound {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hcard : μ.card = n) {B : List (ℕ × ℕ)} (hb : RowBounds μ B) :
    minHeight n B ≤ μ.colLen 0 := by
  have hpos : 0 < μ.colLen 0 := by
    have hc := rowPrefix_eq_card μ (k := 0)
    by_contra h
    have hz := hc (by omega)
    simp only [rowPrefix,Finset.range_zero,Finset.sum_empty] at hz
    omega
  induction B with
  | nil => exact hpos
  | cons p B ih =>
    have hp := hb p (by simp)
    have htail : RowBounds μ B := fun q hq => hb q (by simp [hq])
    simp only [minHeight,List.foldr_cons]
    split_ifs with hh
    · apply max_le _ (ih htail)
      by_contra h
      have := rowPrefix_eq_card μ (show μ.colLen 0 ≤ p.1 by omega)
      omega
    · exact ih htail

lemma rowLen_first_le_prefix (μ : YoungDiagram) {i : ℕ} (hi : 0 < i) :
    μ.rowLen 0 ≤ rowPrefix μ i := by
  have h := rowPrefix_mono μ (show 1 ≤ i from hi)
  simpa [rowPrefix] using h

lemma impossibleBounds_false {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hcard : μ.card = n) {A B : List (ℕ × ℕ)}
    (ha : RowBounds μ.transpose A) (hb : RowBounds μ B)
    (h : impossibleBounds n A B) : False := by
  have hH := minHeight_sound hn μ hcard hb
  have hW := minHeight_sound hn μ.transpose ((transpose_card _).trans hcard) ha
  simp only [YoungDiagram.colLen_transpose] at hW
  rcases h with ⟨p,hp,h⟩ | ⟨q,hq,h⟩ | ⟨p,hp,q,hq,h⟩
  · have hs := (rowLen_first_le_prefix μ.transpose (ha p hp).1).trans (ha p hp).2
    simp only [YoungDiagram.rowLen_transpose] at hs
    omega
  · have hs := (rowLen_first_le_prefix μ (hb q hq).1).trans (hb q hq).2
    omega
  · have hX := endpointBound_sound μ.transpose (ha p hp).1 (ha p hp).2
      (show minHeight n B ≤ μ.transpose.rowLen 0 by simpa using hH)
    have hY := endpointBound_sound μ (hb q hq).1 (hb q hq).2 hW
    have ht := area_le_refined μ (ha p hp).1 (hb q hq).1 (ha p hp).2
      (hb q hq).2 (by simpa using hX) hY hH hW (minHeight_pos n B) (minHeight_pos n A)
    omega

lemma rowPrefix_eq_take (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ k = (μ.rowLens.take k).sum := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [rowPrefix_succ,ih]
    by_cases hk : k < μ.rowLens.length
    · rw [List.take_succ_eq_append_getElem hk, List.sum_append, List.sum_singleton]
      congr 1
      exact YoungDiagram.get_rowLens.symm
    · have hh : μ.colLen 0 ≤ k := by simpa only [YoungDiagram.length_rowLens] using Nat.le_of_not_gt hk
      rw [rowLen_zero_of_height_le μ hh,add_zero]
      rw [List.take_of_length_le (Nat.le_of_not_gt hk),
        List.take_of_length_le (by omega : μ.rowLens.length ≤ k+1)]

lemma not_dominates_witness {μ θ : YoungDiagram} (hc : μ.card = θ.card)
    (h : ¬ Dominates μ θ) :
    ∃ k, 1 ≤ k ∧ k ≤ θ.colLen 0 ∧ rowPrefix μ k < rowPrefix θ k := by
  classical
  obtain ⟨k,hk⟩ := not_forall.mp h
  have hk' : rowPrefix μ k < rowPrefix θ k := Nat.lt_of_not_ge hk
  by_cases hb : k ≤ θ.colLen 0
  · refine ⟨k,?_,hb,hk'⟩
    by_contra ht
    have hz : k = 0 := by omega
    simp [hz,rowPrefix] at hk'
  · refine ⟨θ.colLen 0,?_,le_rfl,?_⟩
    · by_contra ht
      have hz : θ.colLen 0 = 0 := by omega
      have hs := rowPrefix_eq_card θ (le_of_eq hz)
      simp only [rowPrefix,Finset.range_zero,Finset.sum_empty] at hs
      have hu := rowPrefix_le_card θ k
      omega
    · have hle := rowPrefix_mono μ (show θ.colLen 0 ≤ k by omega)
      rw [rowPrefix_eq_card θ (by omega), ← hc] at hk'
      rw [rowPrefix_eq_card θ le_rfl, ← hc]
      omega

lemma coreImpossible_false (μ : YoungDiagram) {K d : ℕ}
    (hd : K ≤ rowPrefix μ d) {A : List (ℕ × ℕ)} (ha : RowBounds μ A)
    (h : coreImpossible K d A) : False := by
  obtain ⟨p,hp,hpd,hpK⟩ := h
  have hle := (hd.trans (rowPrefix_mono μ hpd)).trans (ha p hp).2
  omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_NumericBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric Bands. -/

section

noncomputable section
namespace Saxl.Balance

lemma numericBands_iff {es : List (ℕ × ℕ)} (h : BandsValid es) {e : ℕ × ℕ}
    (he : e ∈ es) {d : ℕ} (z : Fin (d*d)) :
    ((numericBands es h).alphabet d z ∧ (numericBands es h).letterLabel d z = e.1) ↔
      output z ∈ Set.Icc e.1 e.2 := by
  rw [(numericBands es h).letter_iff (mem_bandStarts.mpr ⟨e,he,rfl⟩)]
  rw [show (numericBands es h).upper e.1 = e.2 from bandUpper_eq h he]

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_KroneckerSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kronecker Semigroup. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl
open Columns FlagColumns

lemma tableau_card_eq {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) : μ.card = n := by
  have h := Fintype.card_congr t
  simpa only [Fintype.card_fin,Fintype.card_coe,YoungDiagram.card] using h.symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SquareSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Semigroup. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Columns

lemma kronecker_pos_of_shapes {n : ℕ} {α β μ A B T : YoungDiagram}
    (ha : α = A) (hb : β = B) (ht : μ = T)
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
    (c : Tableau n A) (d : Tableau n B) (u : Tableau n T)
    (h : 0 < kronecker a b t) : 0 < kronecker c d u := by
  let : AddCommGroup (Specht a ⊗[ℂ] Specht b) := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup (Specht c ⊗[ℂ] Specht d) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨F,hF⟩ := (kronecker_pos_iff a b t).mp h
  let e := tensorRepEquiv (spechtShapeEquiv ha a c) (spechtShapeEquiv hb b d)
  let f := spechtShapeEquiv ht.symm u t
  apply (kronecker_pos_iff c d u).mpr
  refine ⟨e.toIntertwiningMap.comp (F.comp f.toIntertwiningMap),?_⟩
  intro hz
  apply hF
  ext x
  apply e.injective
  have hh := congrArg (fun H => H (f.symm x)) hz
  change e (F (f (f.symm x))) = 0 at hh
  change e (F x) = e (0 : Specht a ⊗[ℂ] Specht b)
  have hx : e (F x) = 0 := by simpa only [f.apply_symm_apply] using hh
  exact hx.trans e.toIntertwiningMap.toLinearMap.map_zero.symm

lemma SquareOccurs.card_eq {α μ : YoungDiagram} (h : SquareOccurs α μ) :
    α.card = μ.card := by
  obtain ⟨n,a,t,_⟩ := h
  exact (tableau_card_eq a).trans (tableau_card_eq t).symm

lemma SquareOccurs.pos {n : ℕ} {α μ : YoungDiagram} (h : SquareOccurs α μ)
    (a : Tableau n α) (t : Tableau n μ) : 0 < kronecker a a t := by
  obtain ⟨m,b,u,hu⟩ := h
  have he : m = n := (tableau_card_eq b).symm.trans (tableau_card_eq a)
  subst m
  exact kronecker_pos_of_shapes rfl rfl rfl b b u a a t hu

lemma SquareOccurs.target_transpose {α μ : YoungDiagram}
    (hs : α.transpose = α) (h : SquareOccurs α μ) : SquareOccurs α μ.transpose := by
  have he := h.card_eq
  let a := canonicalTableau α rfl
  let t := canonicalTableau μ he.symm
  exact ⟨α.card,a,transposeTableau t,kronecker_pos_of_shapes rfl rfl rfl _ _ _ _ _ _
    (kronecker_pos_transpose α rfl hs μ he.symm (h.pos a t))⟩

lemma columnShape_perm {rs ss : List ℕ} (h : rs.Perm ss) :
    columnShape rs = columnShape ss := by
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen]
  rw [columnShape_rowLen,columnShape_rowLen,h.countP_eq]

lemma columnShape_diagram (μ : YoungDiagram) :
    columnShape μ.transpose.rowLens = μ := by
  obtain ⟨e,hr,_⟩ := columnShape_placement μ.transpose.rowLens
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen]
  obtain ⟨f,hf,_⟩ := place_columns μ (List.Perm.refl _)
  rw [placed_rowLen e hr,placed_rowLen f hf]

lemma columnShape_sorted (rs : List ℕ) (hs : rs.SortedGE) (hp : ∀ a ∈ rs, 0 < a) :
    columnShape rs = (YoungDiagram.ofRowLens rs hs).transpose := by
  conv_lhs => rw [← YoungDiagram.rowLens_ofRowLens_eq_self hp (hw := hs)]
  simpa only [YoungDiagram.transpose_transpose] using
    columnShape_diagram ((YoungDiagram.ofRowLens rs hs).transpose)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_RowCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowDiagram_eq (rs : List ℕ) (h : GoodRows rs) :
    rowDiagram rs = YoungDiagram.ofRowLens rs h.1 := by
  rw [rowDiagram,columnShape_sorted rs h.1 h.2,YoungDiagram.transpose_transpose]

lemma rowDiagram_rows {rs : List ℕ} (h : GoodRows rs) : (rowDiagram rs).rowLens = rs := by
  rw [rowDiagram_eq rs h,YoungDiagram.rowLens_ofRowLens_eq_self h.2]

lemma rowDiagram_rowLen {rs : List ℕ} (h : GoodRows rs) (i : ℕ) :
    (rowDiagram rs).rowLen i = rs[i]?.getD 0 := by
  rw [rowDiagram_eq rs h,ofRowLens_rowLen]

lemma rowDiagram_height {rs : List ℕ} (h : GoodRows rs) :
    (rowDiagram rs).colLen 0 = rs.length := by
  rw [← YoungDiagram.length_rowLens,rowDiagram_rows h]

lemma rowDiagram_rowLens (μ : YoungDiagram) : rowDiagram μ.rowLens = μ := by
  rw [rowDiagram_eq _ ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

lemma rowsStrip_sound {rs ss : List ℕ} (h : RowsStrip rs ss) :
    HorizontalStrip (rowDiagram rs) (rowDiagram ss) := by
  have hb (i : ℕ) : (rowDiagram rs).rowLen i ≤ (rowDiagram ss).rowLen i ∧
      (rowDiagram ss).rowLen (i+1) ≤ (rowDiagram rs).rowLen i := by
    rw [rowDiagram_rowLen h.1,rowDiagram_rowLen h.2.1,rowDiagram_rowLen h.2.1]
    by_cases hi : i < max rs.length ss.length
    · exact h.2.2 i (List.mem_range.mpr hi)
    · have hr : rs.length ≤ i := le_trans (le_max_left _ _) (Nat.le_of_not_gt hi)
      have hs : ss.length ≤ i := le_trans (le_max_right _ _) (Nat.le_of_not_gt hi)
      simp [List.getElem?_eq_none hr,List.getElem?_eq_none hs,
        List.getElem?_eq_none (by omega : ss.length ≤ i+1)]
  exact horizontal_of_interlacing _ _ (fun i => (hb i).1) (fun i => (hb i).2)

lemma SizedStripChain.trans {bs cs : List ℕ} {ν η μ : YoungDiagram}
    (h : SizedStripChain bs ν η) (h' : SizedStripChain cs η μ) :
    SizedStripChain (bs++cs) ν μ := by
  induction h' with
  | nil => simpa using h
  | snoc hs ht hc ih => simpa [List.append_assoc] using Saxl.SizedStripChain.snoc (ih h) ht hc

lemma chainValid_sound {rs ss : List ℕ} {cs : List (List ℕ)} (h : ChainValid rs cs ss) :
    Saxl.SizedStripChain (stripSizes rs cs) (rowDiagram rs) (rowDiagram ss) := by
  induction cs generalizing rs with
  | nil => have he : rs = ss := h; subst rs; exact Saxl.SizedStripChain.nil _
  | cons us cs ih =>
    have ht : Saxl.SizedStripChain [us.sum-rs.sum] (rowDiagram rs) (rowDiagram us) :=
      Saxl.SizedStripChain.snoc (Saxl.SizedStripChain.nil _) (rowsStrip_sound h.1)
        (by rw [rowDiagram_card,rowDiagram_card]; exact Nat.add_sub_of_le h.2.1)
    exact SizedStripChain.trans ht (ih h.2.2)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_CountedPieri
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counted Pieri. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem placed_strip_restriction_counts {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ (c : Fin b → Fin bs.length) (F : Specht t →ₗ[ℂ] Specht s), Function.Surjective F ∧
      (∀ j, wordContent c j = bs.get j) ∧
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
  refine ⟨cb,F',hF.comp hP, ?_, ?_⟩
  · intro j
    change wordContent cb j = bs[j.val]
    rw [← hcount j.val j.isLt]
    unfold wordContent
    apply Finset.card_bij (fun k _ => p (e.symm (Sum.inr k)))
    · intro k hk
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hk ⊢
      rw [hcR,hk]
    · intro k hk l hl he
      exact Sum.inr.inj (e.symm.injective (p.injective he))
    · intro z hz
      have hcpos : c z = j.val+1 := (Finset.mem_filter.mp hz).2
      obtain ⟨w,rfl⟩ := p.surjective z
      obtain ⟨w,rfl⟩ := e.symm.surjective w
      cases w with
      | inl i => rw [hcL] at hcpos; omega
      | inr k =>
        refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,rfl⟩
        apply Fin.ext
        rw [hcR] at hcpos
        omega
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

lemma orbitTensorEval_injective {b k : ℕ} {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (c : Fin b → Fin k) : Function.Injective (orbitTensorEval (Y := Y) c) :=
  (TensorProduct.piScalarRight ℂ ℂ Y (Fin b → Fin k)).injective.comp
    (TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id Subtype.val_injective)

lemma orbitTensorEval_outer {a b k : ℕ} {Y : Type*}
    [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (Equiv.Perm (Fin a)) Y) (c : Fin b → Fin k)
    (g : Equiv.Perm (Fin a) × Equiv.Perm (Fin b))
    (x : Y ⊗[ℂ] (cyclic (wordRep b k) (Pi.single c 1)).toSubmodule)
    (w : Fin b → Fin k) :
    orbitTensorEval c (outer τ (cyclic (wordRep b k) (Pi.single c 1)).toRepresentation g x) w =
      τ g.1 (orbitTensorEval c x (w ∘ g.2)) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,Pi.add_apply,hx,hy]
  | tmul y z =>
    change orbitTensorEval c (τ g.1 y ⊗ₜ[ℂ]
      (cyclic (wordRep b k) (Pi.single c 1)).toRepresentation g.2 z) w = _
    simp only [orbitTensorEval_tmul,map_smul]
    rfl

lemma orbitTensorMap_eval {n a b k : ℕ} {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) (x : X) :
    orbitTensorEval c (orbitTensorMap e ρ c F x) = bandOrbitMap e ρ c F x := by
  ext w
  simp only [orbitTensorMap,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.flip_apply,TensorProduct.mk_apply,map_sum,Finset.sum_apply,
    orbitTensorEval_tmul]
  change (∑ q : Equiv.Perm (Fin b), (wordRep b k q (Pi.single c 1)) w • _) = _
  simp only [wordRep_single]
  rfl

theorem stripChain_outer_map {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (σ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (K : Representation.IntertwiningMap (spechtRep s) σ) (hK : K ≠ 0) :
    ∃ c : Fin b → Fin bs.length, (∀ j, wordContent c j = bs.get j) ∧
      ∃ L : Representation.IntertwiningMap ((spechtRep t).comp (sumPermHom e))
        (outer σ (cyclic (wordRep b bs.length) (Pi.single c 1)).toRepresentation), L ≠ 0 := by
  obtain ⟨c,F,hF,hc,hFe⟩ := placed_strip_restriction_counts hs s t e
  let F₀ := K.toLinearMap.comp F
  have hFa (h : Equiv.Perm (Fin a)) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e h 1) x) = σ h (F₀ x) := by
    change K (F (spechtRep t (sumPerm e h 1) x)) = σ h (K (F x))
    rw [hFe h 1 rfl,K.isIntertwining]
  let L : Representation.IntertwiningMap ((spechtRep t).comp (sumPermHom e))
      (outer σ (cyclic (wordRep b bs.length) (Pi.single c 1)).toRepresentation) := {
    toLinearMap := orbitTensorMap e (spechtRep t) c F₀
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      apply orbitTensorEval_injective c
      ext w
      simp only [LinearMap.comp_apply]
      rw [orbitTensorMap_eval,orbitTensorEval_outer,orbitTensorMap_eval]
      exact bandOrbitMap_equivariant e (spechtRep t) σ c F₀ hFa g.1 g.2 x w }
  refine ⟨c,hc,L,?_⟩
  have hF₀ : F₀ ≠ 0 := by
    intro hz
    apply hK
    ext x
    obtain ⟨y,rfl⟩ := hF x
    exact LinearMap.congr_fun hz y
  have hFb (q : Equiv.Perm (Fin b)) (hq : c ∘ q = c) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e 1 q) x) = F₀ x := by
    change K (F (spechtRep t (sumPerm e 1 q) x)) = K (F x)
    rw [hFe 1 q hq,map_one]
    rfl
  intro hz
  apply bandOrbitMap_nonzero e (spechtRep t) c F₀ hF₀ hFb
  ext x w
  rw [← orbitTensorMap_eval]
  change orbitTensorEval c (L x) w = 0
  rw [hz]
  simp

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CountedGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counted Gluing. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma wordContent_equiv {n d : ℕ} {w z : Fin n → Fin d}
    (h : ∀ j, wordContent w j = wordContent z j) :
    ∃ q : Equiv.Perm (Fin n), z ∘ q = w := by
  classical
  let f (j : Fin d) : {i : Fin n // w i = j} ≃ {i : Fin n // z i = j} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype,wordContent] using h j)
  let q := (Equiv.sigmaFiberEquiv w).symm.trans
    ((Equiv.sigmaCongrRight f).trans (Equiv.sigmaFiberEquiv z))
  exact ⟨q,funext (fun i => (f (w i) ⟨i,rfl⟩).property)⟩

lemma cyclic_wordContent {n d : ℕ} {w z : Fin n → Fin d}
    (h : ∀ j, wordContent w j = wordContent z j) :
    cyclic (wordRep n d) (Pi.single w 1) = cyclic (wordRep n d) (Pi.single z 1) := by
  obtain ⟨q,hq⟩ := wordContent_equiv h
  have he : wordRep n d q⁻¹ (Pi.single z 1) = Pi.single w 1 := by
    rw [wordRep_single,inv_inv,hq]
  rw [← he,cyclic_action_eq]

lemma coind_outer_map {G H K L X Y W : Type*}
    [Group G] [Group H] [Group K] [Group L]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (G × H) W)
    (φ : K →* G) (ψ : L →* H)
    (σ : Representation ℂ K X) (τ : Representation ℂ L Y)
    (J : Representation.IntertwiningMap ρ
      (outer (Representation.coind φ σ) (Representation.coind ψ τ))) (hJ : J ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ
      (Representation.coind (φ.prodMap ψ) (outer σ τ)), F ≠ 0 := by
  refine ⟨(coindOuter φ ψ σ τ).comp J, ?_⟩
  intro h
  apply hJ
  ext x
  have hx := congrArg (fun f => (f : Representation.IntertwiningMap ρ
    (Representation.coind (φ.prodMap ψ) (outer σ τ))) x) h
  apply coindOuter_injective φ ψ σ τ
  exact hx.trans (map_zero (coindOuter φ ψ σ τ)).symm

lemma coind_composed_map {G H K X W : Type*}
    [Group G] [Group H] [Group K]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (φ : K →* H) (ψ : H →* G)
    (σ : Representation ℂ K X)
    (J : Representation.IntertwiningMap (ρ.comp ψ) (Representation.coind φ σ))
    (hJ : J ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ (Representation.coind (ψ.comp φ) σ), F ≠ 0 := by
  let V := coindLift ψ J
  have hV : V ≠ 0 := coindLift_ne_zero ψ J hJ
  let Z := coindTrans φ ψ σ
  refine ⟨Z.comp V, ?_⟩
  intro hz
  apply hV
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply coindTrans_injective φ ψ σ
  have hx := congrArg (fun f => f x) hz
  exact hx.trans (map_zero Z).symm

theorem coind_product_map {n a b : ℕ} {G H X Y W : Type*}
    [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) W)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (σ : Representation ℂ G X) (τ : Representation ℂ H Y)
    (J : Representation.IntertwiningMap (ρ.comp (sumPermHom e))
      (outer (Representation.coind φ σ) (Representation.coind ψ τ))) (hJ : J ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ
      (Representation.coind ((sumPermHom e).comp (φ.prodMap ψ)) (outer σ τ)), F ≠ 0 := by
  obtain ⟨U,hU⟩ := coind_outer_map (ρ.comp (sumPermHom e)) φ ψ σ τ J hJ
  let : AddCommGroup (X ⊗[ℂ] Y) := Module.addCommMonoidToAddCommGroup ℂ
  exact coind_composed_map ρ (φ.prodMap ψ) (sumPermHom e) (outer σ τ) U hU

theorem outer_coind_map {n a b : ℕ} {G H X Y Z W : Type*}
    [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ Z]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) W)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (σ : Representation ℂ G X) (τ : Representation ℂ H Y)
    (ζ : Representation ℂ (Equiv.Perm (Fin b)) Z)
    (L : Representation.IntertwiningMap (ρ.comp (sumPermHom e))
      (outer (Representation.coind φ σ) ζ)) (hL : L ≠ 0)
    (hQ : SupportLE ζ (Representation.coind ψ τ)) :
    ∃ F : Representation.IntertwiningMap ρ
      (Representation.coind ((sumPermHom e).comp (φ.prodMap ψ)) (outer σ τ)), F ≠ 0 := by
  have hh := (SupportLE.refl (Representation.coind φ σ)).outer hQ
  obtain ⟨J,hJ⟩ := hh.detects_map L hL
  exact coind_product_map ρ e φ ψ σ τ J hJ

theorem stripChain_coind_map {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (σ : Representation ℂ G X) (τ : Representation ℂ H Y)
    (K : Representation.IntertwiningMap (spechtRep s) (Representation.coind φ σ))
    (hK : K ≠ 0) (w : Fin b → Fin bs.length)
    (hw : ∀ j, wordContent w j = bs.get j)
    (hQ : SupportLE (cyclic (wordRep b bs.length) (Pi.single w 1)).toRepresentation
      (Representation.coind ψ τ)) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (Representation.coind ((sumPermHom e).comp (φ.prodMap ψ)) (outer σ τ)), F ≠ 0 := by
  classical
  obtain ⟨c,hc,hLL⟩ := stripChain_outer_map hs s t e (Representation.coind φ σ) K hK
  have he := cyclic_wordContent (fun j => (hc j).trans (hw j).symm)
  rw [he] at hLL
  obtain ⟨L,hL⟩ := hLL
  let := specht_irreducible t
  exact outer_coind_map (spechtRep t) e φ ψ σ τ
    (cyclic (wordRep b bs.length) (Pi.single w 1)).toRepresentation L hL hQ

namespace Balance

theorem Piece.kronecker_pos_of_map {n : ℕ} {G Y : Type*}
    [Group G] [Finite G] [AddCommGroup Y] [Module ℂ Y]
    {lam μ : YoungDiagram} (a : Tableau n lam) (t : Tableau n μ)
    {c : Fin n → ℕ} {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ} {σ : ℕ → ℤ}
    {φ : G →* fiberGroup c} {τ : Representation ℂ G Y}
    (P : Piece (polytabloid a) c A label σ φ τ)
    (ho : ∀ a b, A a → A b → label a < label b → output a < output b)
    (F : Representation.IntertwiningMap (spechtRep t)
      (Representation.coind ((fiberGroup c).subtype.comp φ) τ)) (hF : F ≠ 0) :
    0 < kronecker a a t := by
  have hs := P.support ho (spechtRep t) F hF
  rw [cyclicSquareMap_polytabloid] at hs
  obtain ⟨T,hT⟩ := hs
  let : AddCommGroup (Specht a ⊗[ℂ] Specht a) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨E,hE⟩ := subrepresentation_embeds_of_le_range (spechtTensorMap a a)
    (spechtTensorMap a a).range le_rfl
  exact (kronecker_pos_iff a a t).mpr ⟨E.comp T,intertwining_comp_ne_zero E hE T hT⟩

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_FinitePieri
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Pieri. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance
open FlagColumns Columns

theorem WordPacking.pieri_pos {rs ss ps : List ℕ} {lam L ν μ : YoungDiagram}
    (a : Tableau (rs++ss).sum lam) (s : Tableau rs.sum ν) (t : Tableau (rs++ss).sum μ)
    (e : Cells rs ≃ L.cells) (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hd : L.colLen 0 ≤ lam.colLen 0)
    {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ} {marks : Finset ℕ}
    (Q : WordPacking ss ps (lam.colLen 0) A label marks)
    (k : ℕ) (I : Set ℕ) (hk : k ∉ marks)
    (he : ∀ z, (A z ∧ label z = k) ↔ output z ∈ I)
    (ho : ∀ x y, A x → A y → label x < label y → output x < output y)
    (hv : blocks (rs++ss) (standard (lam.colLen 0)) = polytabloid a)
    (hs : SizedStripChain ps ν μ)
    (F : Representation.IntertwiningMap (spechtRep s)
      (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
        (inOutputs I) (inOutputs_invariant I)).toRepresentation) (hF : F ≠ 0) :
    0 < kronecker a a t := by
  classical
  let W := projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
    (inOutputs I) (inOutputs_invariant I)
  let φ := (fiberGroup (fun _ : Fin rs.sum => k)).subtype.comp (singleFiberHom rs.sum k)
  let ψ := (fiberGroup Q.packing.c).subtype.comp Q.packing.φ
  let : AddCommGroup (Representation.coindV φ W.toRepresentation) := Module.addCommMonoidToAddCommGroup ℂ
  let Z := coindLift (ρ := W.toRepresentation) φ (Representation.IntertwiningMap.id W.toRepresentation)
  have hZ : Function.Injective Z := single_coindLift_injective W.toRepresentation k
  let K := Z.comp F
  have hK : K ≠ 0 := intertwining_comp_ne_zero Z hZ F hF
  obtain ⟨T,hT⟩ := stripChain_coind_map hs s t (appendPositions rs ss) φ ψ
    W.toRepresentation Q.packing.τ K hK Q.word Q.counts Q.packing.support
  let P := placedPiece e hr hc hd k I A label he
  have hdis : ∀ (i : Fin rs.sum) (j : Fin ss.sum), k ≠ Q.packing.c j := by
    intro i j hj
    exact hk (hj ▸ Q.marksBound j)
  let : AddCommGroup (W.toSubmodule ⊗[ℂ] Q.packing.Y) := Module.addCommMonoidToAddCommGroup ℂ
  let R := P.join Q.packing.piece (appendPositions rs ss) hdis
  have hh : positionProduct (appendPositions rs ss) (blocks rs (standard (lam.colLen 0)))
      (blocks ss (standard (lam.colLen 0))) = polytabloid a := by
    rw [← blocks_append,hv]
  rw [hh] at R
  exact R.kronecker_pos_of_map a t ho T hT

end Saxl.Balance

namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns

theorem pieriPlan_pos {n d q δ : ℕ} (p : PackingPlan) {lam : YoungDiagram}
    {rs ss : List ℕ} {cs : List (List ℕ)}
    (hq : 0 < q) (hδ : δ = 1 ∨ δ = 2) (hp : p.Valid d)
    (hb : BandsValid ((q,pairUpper q δ)::p.bands)) (hk : q ∉ p.marks)
    (hh : lam.colLen 0 = d) (hd : q+δ ≤ d)
    (hc : ([q+δ,q]++p.columns).Perm lam.transpose.rowLens)
    (hr : GoodRows rs) (hrl : rs.length ≤ 4) (hrs : rs.sum = 2*q+δ)
    (ho : δ = 2 → ∃ j ∈ List.range (rs.sum+1), (rs.countP (fun x => decide (j < x))) % 2 = 1)
    (hchain : ChainValid rs cs ss) (hs : p.parts.Perm (stripSizes rs cs))
    (a : Tableau n lam) (t : Tableau n (rowDiagram ss)) : 0 < kronecker a a t := by
  obtain ⟨e,he,he'⟩ := place_columns lam hc
  have hn : ([q+δ,q]++p.columns).sum = n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (((enumerate ([q+δ,q]++p.columns)).trans e).trans a.symm)
  subst n
  have hrows : (ShortColumns.shape q δ).rowLens = [q+δ,q] :=
    YoungDiagram.rowLens_ofRowLens_eq_self (by simp; omega)
  obtain ⟨f,hf,hf'⟩ := place_columns (ShortColumns.shape q δ).transpose
    (show [q+δ,q].Perm (ShortColumns.shape q δ).transpose.transpose.rowLens by
      rw [YoungDiagram.transpose_transpose,hrows])
  let s := canonicalTableau (rowDiagram rs)
    (show (rowDiagram rs).card = [q+δ,q].sum by rw [rowDiagram_card,hrs]; simp; omega)
  obtain ⟨F,hF⟩ := short_pair_support q δ (by simp; omega) hδ ((enumerate [q+δ,q]).trans f)
    (rowDiagram rs) s (by rwa [rowDiagram_height hr]) (by
      intro hδ'
      obtain ⟨j,_,hj⟩ := ho hδ'
      exact ⟨j,by simpa only [rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen] using hj⟩)
  let B := numericBands ((q,pairUpper q δ)::p.bands) hb
  obtain ⟨Q⟩ := p.realize hp (B.alphabet d) (B.letterLabel d) (by
    intro v hv z
    exact numericBands_iff hb (List.mem_cons_of_mem _ hv) z)
  let Q' := Q.permute hs
  rw [← hh] at Q'
  let a' := (enumerate ([q+δ,q]++p.columns)).trans e
  have ht : 0 < kronecker a' a' t := WordPacking.pieri_pos a' s t f hf hf'
    (by rw [short_transpose_height,hh]; exact hd) Q' q (Set.Icc q (pairUpper q δ)) hk
    (fun z => numericBands_iff hb (List.mem_cons_self ..) z) (B.letter_ordered _)
    (standard_placed_self e he he') (chainValid_sound hchain) F hF
  exact kronecker_pos_of_shapes rfl rfl rfl a' a' t a a t ht

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_CandidateColumns
attribute [-simp] _root_.OAI.UniversalTensorSquare.candidateRowShuffle_row _root_.OAI.UniversalTensorSquare.candidateSeparatedRow_row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Columns. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

lemma candidate_rowLens {M b δ : ℕ} (hM : 4 ≤ M) :
    (candidate M b δ).rowLens = [M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1 := by
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]
    simp [candidateLengths]
  apply List.ext_getElem
  · simp only [YoungDiagram.length_rowLens,hh,List.length_append,List.length_cons,
      List.length_nil,List.length_reverse,List.length_range',List.length_replicate]
    omega
  · intro i hi hj
    rw [YoungDiagram.get_rowLens,candidate_rowLen _ _ _ _ hM]
    by_cases hi0 : i = 0
    · subst i
      simp [candidateLengths]
    by_cases hi1 : i = 1
    · subst i
      simp [candidateLengths]
    have hi2 : 2 ≤ i := by omega
    have hlen : i < M+b+δ := by simpa only [YoungDiagram.length_rowLens,hh] using hi
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_cons,List.length_nil, Nat.zero_add]
    simp only [candidateLengths,ite_eq_right hi0,ite_eq_right hi1]
    by_cases him : i < M-2
    · rw [ite_eq_left him,List.getElem_append_left (by simp; omega),List.getElem_reverse,
        List.getElem_range']
      simp only [List.length_range',Nat.one_mul]
      omega
    · rw [ite_eq_right him,List.getElem_append_right (by simp; omega)]
      simp only [List.length_reverse,List.length_range']
      by_cases hib : i < M-1+b
      · rw [ite_eq_left hib,List.getElem_append_left (by simp; omega),List.getElem_replicate]
      · rw [ite_eq_right hib,ite_eq_left hlen,List.getElem_append_right (by simp; omega),
          List.getElem_replicate]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_SentinelExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sentinel Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma testWidth_valid_pos {M f : ℕ} (hf : 1 ≤ f) (hw : 0 < testWidth M f) :
    testWidth M f ≤ 8 ∧ f * testWidth M f + 7 + f ≤ 2*M-1 := by
  refine ⟨min_le_left _ _, ?_⟩
  have hh := Nat.mul_le_mul_left f (min_le_right 8 ((2*M-8-f)/f))
  have hh' := Nat.div_mul_le_self (2*M-8-f) f
  have hq : 0 < (2*M-8-f)/f := lt_of_lt_of_le hw (min_le_right _ _)
  have hn : f ≤ 2*M-8-f := by simpa using (Nat.le_div_iff_mul_le (by omega)).mp hq
  unfold testWidth
  nlinarith [Nat.sub_add_cancel (show f ≤ 2*M-8 by omega),
    Nat.sub_add_cancel (show 8 ≤ 2*M by omega),
    Nat.sub_add_cancel (show 1 ≤ 2*M by omega)]

lemma sentinel_height (μ : YoungDiagram) {K : ℕ} (hK : 0 < K) :
    ∃ d, 1 ≤ d ∧ d ≤ 5 ∧ (d ≤ 4 → K ≤ rowPrefix μ d) ∧
      (1 < d → rowPrefix μ (d-1) < K) := by
  by_cases hh : K ≤ rowPrefix μ 4
  · obtain ⟨d,hd,h4,hp,hl⟩ := first_prefix_height μ hK hh
    exact ⟨d,hd,by omega,fun _ => hp,hl⟩
  · exact ⟨5,by decide,le_rfl,by omega,by simpa using Nat.lt_of_not_ge hh⟩

lemma prefixBounds_sound_sentinel (μ : YoungDiagram) {M r d e : ℕ}
    (hM : 1 ≤ M) (hr : 0 < r)
    (hd : 1 < d → colPrefix μ (d-1) < 2*M-1)
    (he : e ≤ 4 → 2*M-1 ≤ rowPrefix μ e) (hfail : ¬BandTest M r μ) :
    ∀ p ∈ prefixBounds M r d e, 0 < p.1 ∧ colPrefix μ p.1 ≤ p.2 := by
  intro p hp
  simp only [prefixBounds,List.mem_append] at hp
  rcases hp with hp | hp
  · split_ifs at hp with hd'
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      subst p
      exact ⟨by omega,by have := hd hd'; dsimp; omega⟩
    · simp at hp
  · obtain ⟨k,hk,hkp⟩ := List.mem_filterMap.mp hp
    simp only [List.mem_range] at hk
    split_ifs at hkp with hke
    · have hp' := Option.some.inj hkp
      subst p
      have hw := testWidth_valid_pos (by omega : 1 ≤ k+1) hke.2
      have hc : bandCapacity μ (k+1) (testWidth M (k+1)) < r := by
        by_contra hh
        apply hfail
        exact ⟨k+1,by omega,by omega,testWidth M (k+1),hw.1,
          (he (by omega)).trans (rowPrefix_mono μ hke.1),hw.2,by omega⟩
      have hb := prefix_le_capacity μ (k+1) (testWidth M (k+1))
      exact ⟨hke.2,by dsimp; omega⟩

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_NumericalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Support. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma headD_rowLens (μ : YoungDiagram) : μ.rowLens.headD 0 = μ.rowLen 0 := by
  have h (xs : List ℕ) : xs.headD 0 = xs[0]?.getD 0 := by cases xs <;> rfl
  rw [h, ← ofRowLens_rowLen μ.rowLens μ.rowLens_sorted,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

lemma transposeRows_rowLens (μ : YoungDiagram) :
    transposeRows μ.rowLens = μ.transpose.rowLens := by
  unfold transposeRows
  rw [headD_rowLens]
  conv_rhs => rw [YoungDiagram.rowLens,YoungDiagram.colLen_transpose]
  apply List.map_congr_left
  intro j _
  rw [YoungDiagram.rowLen_transpose]
  have he := congrArg (fun θ : YoungDiagram => θ.colLen j) (rowDiagram_rowLens μ)
  simpa only [rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen] using he

lemma transposeRows_eq {rs : List ℕ} (h : GoodRows rs) :
    transposeRows rs = (rowDiagram rs).transpose.rowLens := by
  conv_lhs => rw [← rowDiagram_rows h,transposeRows_rowLens]

lemma rowDiagram_transposeRows {rs : List ℕ} (h : GoodRows rs) :
    rowDiagram (transposeRows rs) = (rowDiagram rs).transpose := by
  rw [transposeRows_eq h,rowDiagram_rowLens]

end UniversalTensorSquare

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RegionExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Region Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

theorem semantic_capacity_dichotomy (μ θ : YoungDiagram) {n M r : ℕ}
    (hn : 0 < n) (hM : 1 ≤ M) (hr : 0 < r) (hc : μ.card = n) (ht : θ.card = n)
    (P : List ℕ → Prop)
    (check : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range θ.rowLens.length, ∀ b ∈ List.range θ.rowLens.length,
        semanticResidualCheck n M r (d+1) (e+1) (a+1) (b+1) θ.rowLens P) :
    BandTest M r μ ∨ BandTest M r μ.transpose ∨ Dominates μ θ ∨
      Dominates μ.transpose θ ∨ P μ.rowLens := by
  classical
  by_contra hh
  push Not at hh
  rcases hh with ⟨hband,hband',hdom,hdom',hP⟩
  obtain ⟨d,hd,hd',hHd,hHd'⟩ := sentinel_height μ.transpose (show 0 < 2*M-1 by omega)
  obtain ⟨e,he,he',hWe,hWe'⟩ := sentinel_height μ (show 0 < 2*M-1 by omega)
  obtain ⟨a,ha,ha',hA⟩ := not_dominates_witness ((transpose_card _).trans hc |>.trans ht.symm) hdom'
  obtain ⟨b,hb,hb',hB⟩ := not_dominates_witness (hc.trans ht.symm) hdom
  have hAf := prefixBounds_sound_sentinel μ hM hr hHd' hWe hband
  have hBf := prefixBounds_sound_sentinel μ.transpose hM hr
    (by simpa only [colPrefix,YoungDiagram.transpose_transpose] using hWe') hHd hband'
  let A := prefixBounds M r d e ++ [(a,(θ.rowLens.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(θ.rowLens.take b).sum-1)]
  have hAbb : RowBounds μ.transpose A := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hAf p hp
    · have heq : p = (a,(θ.rowLens.take a).sum-1) := by simpa using hp
      subst p
      rw [rowPrefix_eq_take θ] at hA
      exact ⟨ha,by dsimp; omega⟩
  have hBbb : RowBounds μ B := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · simpa only [colPrefix,YoungDiagram.transpose_transpose] using hBf p hp
    · have heq : p = (b,(θ.rowLens.take b).sum-1) := by simpa using hp
      subst p
      rw [rowPrefix_eq_take θ] at hB
      exact ⟨hb,by dsimp; omega⟩
  have h := check (d-1) (by simp; omega) (e-1) (by simp; omega)
    (a-1) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
    (b-1) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
  have hde : d-1+1 = d := by omega
  have hee : e-1+1 = e := by omega
  have hae : a-1+1 = a := by omega
  have hbe : b-1+1 = b := by omega
  rw [hde,hee,hae,hbe] at h
  rcases h with ⟨h4,h⟩ | ⟨h4,h⟩ | h | h
  · exact coreImpossible_false μ.transpose (hHd h4) hAbb h
  · exact coreImpossible_false μ (hWe h4) hBbb h
  · exact impossibleBounds_false hn μ hc hAbb hBbb h
  · exact hP (h μ hc hAbb hBbb)

theorem candidate_semantic_pos {n M b δ r : ℕ} (hM : 4 ≤ M)
    (hδ : δ ≤ 1) (hr : r = 2*b+δ) (hrpos : 0 < r)
    (hn : (candidate M b δ).card = n)
    (q : List ℕ) (hq : GoodRows q) (hqn : q.sum = n)
    (p : PackingPlan) (hv : p.Valid (M+b+δ)) (hbands : BandsValid p.bands)
    (hcols : p.columns.Perm ([M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
    (hparts : p.parts.Perm q) (P : List ℕ → Prop)
    (hP : ∀ rs, GoodRows rs → rs.sum = n → P rs → SquareOccurs (candidate M b δ) (rowDiagram rs))
    (check : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range q.length, ∀ c ∈ List.range q.length,
        semanticResidualCheck n M r (d+1) (e+1) (a+1) (c+1) q P)
    (μ : YoungDiagram) (hμ : μ.card = n) :
    0 < kronecker (canonicalTableau (candidate M b δ) hn)
      (canonicalTableau (candidate M b δ) hn) (canonicalTableau μ hμ) := by
  have hposn : 0 < n := by rw [← hn,candidate_card _ _ _ (by omega)]; omega
  have hp : ∀ a ∈ p.parts, 0 < a := fun a ha => hq.2 a (hparts.mem_iff.mp ha)
  have hshape : (columnShape p.parts).transpose = rowDiagram q := by
    rw [columnShape_perm hparts]; rfl
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]; simp [candidateLengths]
  have hc : p.columns.Perm (candidate M b δ).transpose.rowLens := by
    rw [candidate_transpose,candidate_rowLens hM]; exact hcols
  have cone (ν : YoungDiagram) (hν : ν.card = n) (hd : Dominates ν (rowDiagram q)) :
      0 < kronecker (canonicalTableau (candidate M b δ) hn)
        (canonicalTableau (candidate M b δ) hn) (canonicalTableau ν hν) := by
    apply packingPlan_pos p hv hbands hh hc hp
    simpa only [hshape] using hd
  have htcheck : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range (rowDiagram q).rowLens.length, ∀ c ∈ List.range (rowDiagram q).rowLens.length,
        semanticResidualCheck n M r (d+1) (e+1) (a+1) (c+1) (rowDiagram q).rowLens P := by
    simpa only [rowDiagram_rows hq] using check
  rcases semantic_capacity_dichotomy μ (rowDiagram q) hposn (by omega) hrpos hμ
    ((rowDiagram_card q).trans hqn) P htcheck with h | h | h | h | h
  · exact band_kronecker_pos hM hδ hr _ μ _ h
  · apply (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr
    exact band_kronecker_pos hM hδ hr _ μ.transpose _ h
  · exact cone μ hμ h
  · apply (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr
    exact cone μ.transpose ((transpose_card μ).trans hμ) h
  · have ht := hP μ.rowLens ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩
      ((card_eq_sum_rowLens μ).symm.trans hμ) h
    rw [rowDiagram_rowLens] at ht
    exact ht.pos _ _

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ResidualTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual Trees. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

namespace RowTree

lemma find_sound {P : List ℕ → Prop} {t : RowTree} (h : t.All P)
    {rs : List ℕ} (hf : t.find rs = true) : P rs := by
  induction t with
  | empty => simp [find] at hf
  | node key l r hl hr =>
    simp only [find] at hf
    obtain ⟨hk,hL,hR⟩ := h
    split_ifs at hf with he hc
    · simpa only [he] using hk
    · exact hl hL hf
    · exact hr hR hf

end RowTree

lemma treeResidual_sound {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hn : (candidate M b δ).card = n) (hre : r = 2*b+δ)
    {qs : List (List ℕ)} {t : RowTree}
    (hcones : ∀ q ∈ qs, ∀ μ : YoungDiagram, μ.card = n →
      RowsDom μ.rowLens q → SquareOccurs (candidate M b δ) μ)
    (htree : t.All (fun rs => SquareOccurs (candidate M b δ) (rowDiagram rs)))
    {rs : List ℕ} (hgood : GoodRows rs) (hsum : rs.sum = n)
    (h : TreeResidual M r qs t rs) : SquareOccurs (candidate M b δ) (rowDiagram rs) := by
  rcases h with h | h | h
  · exact residualProperty_sound hM hδ hn hre hcones (by simp) hgood hsum h
  · exact RowTree.find_sound htree h
  · have hh := RowTree.find_sound htree h
    rw [rowDiagram_transposeRows hgood] at hh
    simpa only [YoungDiagram.transpose_transpose] using
      hh.target_transpose (candidate_transpose M b δ)

lemma rowDiagram_candidate {M b δ : ℕ} (hM : 4 ≤ M) :
    rowDiagram ([M+b+δ,M-1+b] ++ (List.range' 3 (M-4)).reverse ++
      List.replicate (b+1) 2 ++ List.replicate (1+δ) 1) = candidate M b δ := by
  rw [← candidate_rowLens hM, rowDiagram_rowLens]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PieriCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pieri Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowSquare_pieri {p rs ss : List ℕ} {cs : List (List ℕ)}
    (plan : PackingPlan) (q δ : ℕ)
    (hp : GoodRows p) (hq : 0 < q) (hδ : δ = 1 ∨ δ = 2)
    (hv : plan.Valid p.length) (hb : BandsValid ((q,pairUpper q δ)::plan.bands))
    (hk : q ∉ plan.marks) (hd : q+δ ≤ p.length)
    (hc : ([q+δ,q]++plan.columns).Perm (transposeRows p))
    (hr : GoodRows rs) (hrl : rs.length ≤ 4) (hrs : rs.sum = 2*q+δ)
    (ho : δ = 2 → ∃ j ∈ List.range (rs.sum+1),
      (rs.countP (fun x => decide (j < x))) % 2 = 1)
    (hchain : ChainValid rs cs ss) (hs : plan.parts.Perm (stripSizes rs cs))
    (hn : ss.sum = p.sum) : RowSquare p ss := by
  let a := canonicalTableau (rowDiagram p) (rowDiagram_card p)
  let t := canonicalTableau (rowDiagram ss) ((rowDiagram_card ss).trans hn)
  refine ⟨p.sum,a,t,?_⟩
  apply pieriPlan_pos plan hq hδ hv hb hk (rowDiagram_height hp) hd
  · rwa [← transposeRows_eq hp]
  · exact hr
  · exact hrl
  · exact hrs
  · exact ho
  · exact hchain
  · exact hs

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones118 : ∀ q ∈ degreeQs118, ∀ μ : YoungDiagram, μ.card = 118 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 12 10 0) μ := by
  intro q hq
  simp only [degreeQs118,List.not_mem_nil] at hq

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_PieriRows118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pieri Rows 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma pieriLowerValid118 : pieriLower118.Valid 22 := by decide +kernel

lemma pieriSquare118_0 : RowSquare [22,21,10,9,8,7,6,5,4,3,2,2,2,2,2,2,2,2,2,2,2,1] [11,11,11,11,11,11,11,11,10,10,10] := by
  exact rowSquare_pieri (rs := [11,11,11,10]) (cs := [[11,11,11,11,8],[11,11,11,11,11,6],[11,11,11,11,11,11,3],[11,11,11,11,11,11,8],[11,11,11,11,11,11,11,2],[11,11,11,11,11,11,11,7],[11,11,11,11,11,11,11,11],[11,11,11,11,11,11,11,11,4],[11,11,11,11,11,11,11,11,8],[11,11,11,11,11,11,11,11,10,2],[11,11,11,11,11,11,11,11,10,6],[11,11,11,11,11,11,11,11,10,9],[11,11,11,11,11,11,11,11,10,10,2],[11,11,11,11,11,11,11,11,10,10,5],[11,11,11,11,11,11,11,11,10,10,8],[11,11,11,11,11,11,11,11,10,10,10]]) pieriLower118 21 1
    (by decide) (by decide) (by decide) pieriLowerValid118 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

lemma pieriSquare118_1 : RowSquare [22,21,10,9,8,7,6,5,4,3,2,2,2,2,2,2,2,2,2,2,2,1] [11,11,11,11,11,11,11,11,11,10,9] := by
  exact rowSquare_pieri (rs := [11,11,11,10]) (cs := [[11,11,11,11,8],[11,11,11,11,11,6],[11,11,11,11,11,11,3],[11,11,11,11,11,11,8],[11,11,11,11,11,11,11,2],[11,11,11,11,11,11,11,7],[11,11,11,11,11,11,11,11],[11,11,11,11,11,11,11,11,4],[11,11,11,11,11,11,11,11,8],[11,11,11,11,11,11,11,11,11,1],[11,11,11,11,11,11,11,11,11,5],[11,11,11,11,11,11,11,11,11,8],[11,11,11,11,11,11,11,11,11,10,1],[11,11,11,11,11,11,11,11,11,10,4],[11,11,11,11,11,11,11,11,11,10,7],[11,11,11,11,11,11,11,11,11,10,9]]) pieriLower118 21 1
    (by decide) (by decide) (by decide) pieriLowerValid118 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree118_0All : degreeTree118_0.All (RowSquare [22,21,10,9,8,7,6,5,4,3,2,2,2,2,2,2,2,2,2,2,2,1]) := by
  exact ⟨pieriSquare118_1,⟨pieriSquare118_0,True.intro,True.intro⟩,True.intro⟩

lemma degreeTreeAll118 : degreeTree118.All
    (fun rs => SquareOccurs (candidate 12 10 0) (rowDiagram rs)) := by
  have hp : rowDiagram [22,21,10,9,8,7,6,5,4,3,2,2,2,2,2,2,2,2,2,2,2,1] = candidate 12 10 0 := rowDiagram_candidate (M := 12) (b := 10) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree118_0All

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos118_oai (μ : YoungDiagram) (hμ : μ.card = 118) :
    0 < kronecker (canonicalTableau (candidate 12 10 0) degreeCard118)
      (canonicalTableau (candidate 12 10 0) degreeCard118) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 20) (by decide) (by decide) rfl (by decide)
    degreeCard118 degreeRows118_0 (by decide) (by decide)
    degreePlan118_0 (by decide) (by decide) (by decide) (by decide) degreeP118 ?_
    degreeCheck118 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard118 rfl degreeCones118
    degreeTreeAll118 hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos118_oai := @OAI.UniversalTensorSquare.degree_pos118_oai
