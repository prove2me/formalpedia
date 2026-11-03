-- Prove2me | solution 1 for compact_lie_virtually_abelian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:25:04.29286+00:00
-- url     : https://prove2.me/submissions/3dba3fbc-e50b-4739-89e5-7cddea534a5c

import Mathlib
import Definitions.Def_OAIQ093D000
import Definitions.Def_OAIQ093D001
import Theorems.Thm_HnEpsData_central_trivial_virtually_abelian
import Theorems.Thm_centralizer_iso
import Theorems.Thm_poly_growth_equiv
import Theorems.Thm_volume_packing

section
-- module Solutions.OAIQ093_PR.UnitaryGromov
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Compact Lie subgroups of polynomial growth are virtually abelian

`compact_lie_virtually_abelian`.

Root of the `Gromov.Unitary` hierarchy.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 2000000 in
lemma compact_lie_virtually_abelian_oai (n : ℕ) (hn : n ≠ 0) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (G_FG : G.FG)
  (S_data: SPolyData G): ∃ N : Subgroup G, IsMulCommutative N ∧ N.FiniteIndex := by


  -- This will get used for the 'h_n_eps_data' variable via instance synthesis
  let _ : HnEpsData := {
    degree := S_data.S_poly_deg
  }

  by_cases n_eq_one : n = 1
  · have fin_sin_subsingleton : Subsingleton (Fin n) := by
      rw [n_eq_one]
      exact Fin.subsingleton_one
    have all_diag : ∀ h : G, h.val.val.IsDiag := by
      intro h
      apply Matrix.isDiag_of_subsingleton

    have all_comm : ∀ (a b : G), a.val.val * b.val.val = b.val.val * a.val.val := by
      intro a b
      have diag_a := all_diag a
      have diag_b := all_diag b
      rw [Matrix.isDiag_iff_diagonal_diag] at diag_a
      rw [Matrix.isDiag_iff_diagonal_diag] at diag_b
      rw [← diag_a, ← diag_b]
      simp
      intro i
      rw [mul_comm]

    use ⊤
    refine ⟨?_, ?_⟩
    · exact {
        is_comm := by
          exact {
            comm := by
              intro a b
              rw [Subtype.ext_iff]
              simp
              rw [Subtype.ext_iff]
              simp
              rw [Subtype.ext_iff]
              simp
              apply all_comm
          }
      }
    · exact Subgroup.instFiniteIndexTop
  · have nontrivial_centrer_implies_virtual (G : Subgroup ↥(Matrix.unitaryGroup (Fin n) ℂ)) (G_FG : G.FG) (S_data: SPolyData G) (nontrivial_central : ∃ g : G, (∀ z : ℂ, g.val.val ≠ z • 1) ∧ g ∈ Set.center G): ∃ N : Subgroup G, IsMulCommutative ↥N ∧ N.FiniteIndex := by
      obtain ⟨g, g_not_multiple_I, g_central⟩ := nontrivial_central


      have all_mem_central : ∀ a : G, a ∈ Subgroup.centralizer {g} := by
        intro a b b_mem
        simp at b_mem
        rw [b_mem]
        rw [Set.mem_center_iff] at g_central
        have g_comm := g_central.comm a
        exact g_comm

      have n_ge_two : 2 ≤ n := by
        omega

      have n_ne_zero: NeZero n := by
        exact { out := hn }
      obtain ⟨data⟩ := centralizer_iso G g g_not_multiple_I


      -- The abelian subgroup of G_i.
      -- TODO - we need to construct a generating set for the smaller subgroup
      -- TODO - is there existing API for this in mathlib?
      let g_to_central: G →* (Subgroup.centralizer {g.val}) := {
        toFun := fun a => ⟨a, by
          rw [Subgroup.mem_centralizer_iff]
          simp
          rw [Set.mem_center_iff] at g_central
          rw [isMulCentral_iff] at g_central
          have foo := (g_central.1) a
          rw [commute_iff_eq] at foo
          rw [Subtype.ext_iff] at foo
          simpa using foo
        ⟩,
        map_one' := by
          simp
        map_mul' := by
          simp
      }

      have ha := data.ha

      let new_A_map := (Subgroup.subtype _).comp ((MonoidHom.fst _ _).comp (data.iso.toMonoidHom.comp g_to_central))
      let new_B_map := (Subgroup.subtype _).comp ((MonoidHom.snd _ _).comp (data.iso.toMonoidHom.comp g_to_central))

      let first_new_data: SPolyData (new_A_map.range) := {
        S := new_A_map.rangeRestrict '' S_data.S,
        S_one := by
          simp only [Set.mem_image]
          use 1
          refine ⟨?_, ?_⟩
          . apply S_data.S_one
          . exact map_one _
        S_inv := by
          rw [← Set.image_inv]
          rw [← S_data.S_inv]
        S_finite := by
          apply Set.Finite.image
          apply S_data.S_finite
        S_generates := by
          rw [← MonoidHom.map_closure]
          rw [S_data.S_generates]
          rw [Subgroup.map_top_of_surjective]
          exact MonoidHom.rangeRestrict_surjective new_A_map
        S_poly_const := S_data.S_poly_const
        S_poly_const_pos := S_data.S_poly_const_pos
        S_poly_deg := S_data.S_poly_deg
        S_poly := by
          intro r hr
          rw [Set.Finite.toFinset_image]
          rw [← Finset.image_pow]
          grw [Finset.card_image_le]
          .
            apply S_data.S_poly r hr
          . exact S_data.S_finite
      }

      have data_b_pos: 0 < data.b := by
        have hab := data.hb
        omega

      -- TODO - deduplicate 'first_new_data' and 'second_new_data'
      let second_new_data: SPolyData (new_B_map.range) := {
        S := new_B_map.rangeRestrict '' S_data.S,
        S_one := by
          simp only [Set.mem_image]
          use 1
          refine ⟨?_, ?_⟩
          . apply S_data.S_one
          . exact map_one _
        S_inv := by
          rw [← Set.image_inv]
          rw [← S_data.S_inv]
        S_finite := by
          apply Set.Finite.image
          apply S_data.S_finite
        S_generates := by
          rw [← MonoidHom.map_closure]
          rw [S_data.S_generates]
          rw [Subgroup.map_top_of_surjective]
          exact MonoidHom.rangeRestrict_surjective new_B_map
        S_poly_const := S_data.S_poly_const
        S_poly_const_pos := S_data.S_poly_const_pos
        S_poly_deg := S_data.S_poly_deg
        S_poly := by
          intro r hr
          rw [Set.Finite.toFinset_image]
          rw [← Finset.image_pow]
          grw [Finset.card_image_le]
          .
            apply S_data.S_poly r hr
          . exact S_data.S_finite
      }

      obtain ⟨first_subgroup, first_subgroup_abelian, first_subgroup_finite_index⟩ := compact_lie_virtually_abelian_oai (data.a) (by grind) (new_A_map.range) (by
        rw [← Group.fg_iff_subgroup_fg]
        rw [← Group.fg_iff_subgroup_fg] at G_FG
        apply Group.fg_range
      ) (first_new_data)
      obtain ⟨second_subgroup, second_subgroup_abelian, second_subgroup_finite_index⟩ := compact_lie_virtually_abelian_oai (data.b) (by grind) (new_B_map.range) (by
        rw [← Group.fg_iff_subgroup_fg]
        rw [← Group.fg_iff_subgroup_fg] at G_FG
        apply Group.fg_range
      ) (second_new_data)

      let iso := Subgroup.map data.iso.symm.toMonoidHom

      let G_1 := (Subgroup.comap new_A_map.rangeRestrict first_subgroup)
      let G_2 := (Subgroup.comap new_B_map.rangeRestrict second_subgroup)

      have g_1_finite_index: G_1.FiniteIndex := by
        unfold G_1
        rw [Subgroup.finiteIndex_iff]
        rw [Subgroup.index_comap_of_surjective]
        .
          rw [← Subgroup.finiteIndex_iff]
          apply first_subgroup_finite_index
        . exact MonoidHom.rangeRestrict_surjective new_A_map

      have g_2_finite_index: G_2.FiniteIndex := by
        unfold G_2
        rw [Subgroup.finiteIndex_iff]
        rw [Subgroup.index_comap_of_surjective]
        .
          rw [← Subgroup.finiteIndex_iff]
          apply second_subgroup_finite_index
        . exact MonoidHom.rangeRestrict_surjective new_B_map


      let G' := G_1 ⊓ G_2

      have G'_finite_index : G'.FiniteIndex := by
        unfold G'
        infer_instance


      have G'_abeliean : IsMulCommutative G' := by
        unfold G'
        refine { is_comm := ?_ }
        refine { comm := ?_ }
        intro a b
        have a_mem := a.property
        have b_mem := b.property
        rw [Subgroup.mem_inf] at a_mem b_mem
        have a_first := a_mem.1
        have b_first := b_mem.1
        have a_second := a_mem.2
        have b_second := b_mem.2
        unfold G_1 at a_first b_first
        unfold G_2 at a_second b_second

        rw [Subgroup.mem_comap] at a_first b_first

        have first_comm := first_subgroup_abelian.is_comm.comm ⟨_, a_first⟩ ⟨_, b_first⟩
        have second_comm := second_subgroup_abelian.is_comm.comm ⟨_, a_second⟩ ⟨_, b_second⟩

        rw [Subtype.ext_iff]
        simp
        apply_fun g_to_central
        simp
        apply_fun data.iso
        .
          simp
          apply Prod.ext
          . simp
            rw [Subtype.ext_iff]
            simp
            exact congrArg (fun x : ↥first_subgroup => x.val.val) first_comm
          . simp
            rw [Subtype.ext_iff]
            simp
            exact congrArg (fun x : ↥second_subgroup => x.val.val) second_comm
        . intro a b hab
          simp [g_to_central] at hab
          simpa using hab

      use G'
    by_cases nontrivial_central : ∃ g : G, (∀ z : ℂ, g.val.val ≠ z • 1) ∧ g ∈ Set.center G
    · exact nontrivial_centrer_implies_virtual G G_FG S_data nontrivial_central
    · -- Case two - we have no non-trivial central elements

      have two_le_n: 2 ≤ n := by
        omega
      simp only [ne_eq, not_exists, not_and] at nontrivial_central
      let ε: ℝ := (HnEpsData.H_n_eps two_le_n)
      have hε : 0 < ε := by
        simp [ε]
        apply HnEpsData.H_n_eps_pos

      obtain ⟨C, G_eps⟩:= volume_packing n (by omega) ε hε
      specialize G_eps G

      have new_G_FG: Group.FG G := by
        exact (Group.fg_iff_subgroup_fg G).mpr G_FG

      have G'_finite := G_eps.1
      have G'_fg := Subgroup.fg_of_index_ne_zero (G' n ε G)

      obtain ⟨pre_S, h_pre_S⟩ := G'_fg

      have pos := S_data.S_poly_const_pos
      have my_equiv := poly_growth_equiv S_data.S_poly_const S_data.S_poly_deg (by omega)
        S_data.S_finite.toFinset (Finset.image (Subgroup.subtype _) (pre_S ∪ pre_S⁻¹ ∪ {1})) ?_ ?_ (by simp [S_data.S_generates]) S_data.S_poly

      obtain ⟨b, hb, new_poly⟩ := my_equiv

      let S_data_G': SPolyData ((G' n ε G)) := {
        S := pre_S ∪ pre_S⁻¹ ∪ {1},
        S_finite := by simp,
        S_generates := by
          rw [Subgroup.closure_union]
          rw [Subgroup.closure_union]
          simp [h_pre_S]
        S_one := by
          simp
        S_inv := by
          simp
          rw [Set.union_comm]
        S_poly_const := b
        S_poly_const_pos := by omega
        S_poly_deg := S_data.S_poly_deg
        S_poly := by
          intro r hr
          unfold Set.Finite.toFinset
          specialize new_poly r hr
          rw [← Finset.image_pow] at new_poly
          rw [Finset.card_image_of_injective] at new_poly
          -- TODO(mathlib) - figure out what @[norm_cast] attribute to apply to make 'norm_cast' work with the {1} set
          have one_eq: ({1}: Set (G' n ε G)) = ({1}: Finset (G' n ε G)) := by simp
          norm_cast
          simp_rw [one_eq]
          norm_cast
          . simpa using new_poly
          . exact subtype_injective (G' n ε G)
      }

      let map_set (Q: Finset (G' n ε G)) := Finset.image (fun a => (⟨a.val, by simp⟩ : (Subgroup.map G.subtype (G' n ε G)))) Q
      let other := G.subtype '' (((G' n ε G).subtype) '' (pre_S))


      by_cases G'_nontrivial_central : ∃ g : (G' n ε G), (∀ z : ℂ, g.val.val.val ≠ z • 1) ∧ g ∈ Set.center (G' n ε G)
      ·
        let foo := S_data_G'.S
        let bar := G.subtype.subgroupMap (G' n ε G)
        have subtype_S_data: SPolyData (Subgroup.map G.subtype (G' n ε G)) := {
          S := (G.subtype.subgroupMap (G' n ε G)) '' S_data_G'.S
          S_finite := by
            apply Set.Finite.image
            apply S_data_G'.S_finite
          S_one := by
            simp only [Set.mem_image]
            use 1
            simp
            apply S_data_G'.S_one
          S_inv := by
            rw [← Set.image_inv]
            rw [← S_data_G'.S_inv]
          S_generates := by
            rw [← MonoidHom.map_closure]
            rw [S_data_G'.S_generates]
            rw [Subgroup.map_top_of_surjective]
            exact MonoidHom.subgroupMap_surjective G.subtype (G' n ε G)
          S_poly_const := S_data_G'.S_poly_const
          S_poly_const_pos := S_data_G'.S_poly_const_pos
          S_poly_deg := S_data_G'.S_poly_deg
          S_poly := by
            intro r hr
            rw [Set.Finite.toFinset_image]
            rw [← Finset.image_pow]
            grw [Finset.card_image_le]
            .
              apply S_data_G'.S_poly r hr
            . exact S_data_G'.S_finite
        }

        have G'_virtual := nontrivial_centrer_implies_virtual (Subgroup.map G.subtype (G' n ε G)) (by
          have G'_finite := G_eps.1
          have G_FG_other : Group.FG G := by
            exact (Group.fg_iff_subgroup_fg G).mpr G_FG
          have G'_FG := Subgroup.fg_of_index_ne_zero (G' n ε G)
          -- TODO - PR this to mathlib
          rw [Subgroup.fg_iff_submonoid_fg]
          apply Submonoid.FG.map
          rw [← Subgroup.fg_iff_submonoid_fg]
          exact (Group.fg_iff_subgroup_fg (G' n ε G)).mp G'_FG
        ) (subtype_S_data) (by
          obtain ⟨g, hg⟩ := G'_nontrivial_central
          use ⟨g, by simp⟩
          refine ⟨?_, ?_⟩
          · intro z
            simp
            have g_prop := hg.1 z
            simpa using g_prop
          · have g_mem := hg.2
            rw [Set.mem_center_iff]
            rw [Set.mem_center_iff] at g_mem
            exact {
              comm := by
                -- TODO - make this less horrible
                intro a
                obtain ⟨b, b_mem, b_map⟩ := Subgroup.mem_map.mpr a.property
                simpa [Subtype.ext_iff, commute_iff_eq, ← b_map] using g_mem.comm ⟨b, b_mem⟩
              left_assoc := by intros; group
              right_assoc := by intros; group
            }
        )
        obtain ⟨N, N_comm, N_finite_index⟩ := G'_virtual

        have G'_iso := Subgroup.equivMapOfInjective (G' n ε G) G.subtype (by simp)
        let G'_hom := G'_iso.symm.toMonoidHom
        refine ⟨Subgroup.map (Subgroup.subtype _) <| Subgroup.map G'_hom N, ?_, ?_⟩
        · simp [G'_hom]
          apply Subgroup.map_isMulCommutative
        · rw [Subgroup.finiteIndex_iff, Subgroup.index_map]
          rw [Subgroup.finiteIndex_iff] at N_finite_index G_eps
          simpa [G'_hom] using ⟨N_finite_index, G_eps.1⟩


      ·


        simp at hn
        have target := HnEpsData.central_trivial_virtually_abelian n (by omega) G G_FG ?_ G_eps.1 S_data_G' ?_
        · exact target
        · intro g hg
          simp only [ne_eq, not_exists, not_and] at G'_nontrivial_central
          specialize G'_nontrivial_central g
          rw [← not_imp_not] at G'_nontrivial_central
          simp at G'_nontrivial_central
          exact G'_nontrivial_central hg
        . rfl
      .
        ext a
        simp
        nth_rw 1 [S_data.S_inv]
        simp
      . simp
        apply S_data.S_one
termination_by (n, G.index)
decreasing_by
  · apply Prod.Lex.left
    have hab := data.hab
    grind
  . apply Prod.Lex.left
    have hab := data.hab
    grind
end

theorem solution : type_of% @compact_lie_virtually_abelian_oai := @compact_lie_virtually_abelian_oai
