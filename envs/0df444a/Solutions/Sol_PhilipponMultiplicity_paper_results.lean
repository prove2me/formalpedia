-- Prove2me | solution 1 for PhilipponMultiplicity.paper_results
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T11:21:32.794992+00:00
-- url     : https://prove2.me/submissions/202ac51c-0c4e-4cf5-9605-009b7bf23e5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PhilipponMultiplicity_SourceStatements
import Theorems.Thm_PhilipponMultiplicity_theorem_2_1
import Theorems.Thm_PhilipponMultiplicity_corollary_2_2
import Theorems.Thm_PhilipponMultiplicity_corollary_2_3
import Theorems.Thm_PhilipponMultiplicity_lemma_3_1_positive_equation_degrees
import Theorems.Thm_PhilipponMultiplicity_lemma_3_2
import Theorems.Thm_PhilipponMultiplicity_proposition_3_3
import Theorems.Thm_PhilipponMultiplicity_lemma_3_4
import Theorems.Thm_PhilipponMultiplicity_proposition_4_3
import Theorems.Thm_PhilipponMultiplicity_proposition_4_4
import Theorems.Thm_PhilipponMultiplicity_lemma_4_5
import Theorems.Thm_PhilipponMultiplicity_lemma_4_6
import Theorems.Thm_PhilipponMultiplicity_proposition_4_7
import Theorems.Thm_PhilipponMultiplicity_lemma_5_1
import Theorems.Thm_PhilipponMultiplicity_addendum_strengthened_vanishing
import Theorems.Thm_PhilipponMultiplicity_addendum_converse
import Theorems.Thm_PhilipponMultiplicity_section_three_foundations
import Theorems.Thm_PhilipponMultiplicity_mixed_degree_geometry
import Theorems.Thm_PhilipponMultiplicity_section_three_counterexample
import Theorems.Thm_PhilipponMultiplicity_lemma_3_1_zero_degree_counterexample
import Theorems.Thm_PhilipponMultiplicity_translation_operator_foundations
import Theorems.Thm_PhilipponMultiplicity_translation_geometry_remarks
import Theorems.Thm_PhilipponMultiplicity_analytic_contact_invariance
import Theorems.Thm_PhilipponMultiplicity_corollary_counting_estimates
import Theorems.Thm_PhilipponMultiplicity_section_five_construction
import Theorems.Thm_PhilipponMultiplicity_masser_wustholz_recovery
import Theorems.Thm_PhilipponMultiplicity_source_boundary_counterexamples

set_option autoImplicit false
set_option maxRecDepth 4096
namespace PhilipponMultiplicity.FullPaperAssembly
universe u

/-- Conjoin the literal source statements, retaining every hypothesis and universe. -/
theorem assemble
    (h0 : SourceStatements.theorem_2_1.{u})
    (h1 : SourceStatements.corollary_2_2.{u})
    (h2 : SourceStatements.corollary_2_3.{u})
    (h3 : SourceStatements.lemma_3_1_positive_equation_degrees.{u})
    (h4 : SourceStatements.lemma_3_2.{u})
    (h5 : SourceStatements.proposition_3_3.{u})
    (h6 : SourceStatements.lemma_3_4.{u})
    (h7 : SourceStatements.proposition_4_3.{u})
    (h8 : SourceStatements.proposition_4_4.{u})
    (h9 : SourceStatements.lemma_4_5.{u})
    (h10 : SourceStatements.lemma_4_6.{u})
    (h11 : SourceStatements.proposition_4_7.{u})
    (h12 : SourceStatements.lemma_5_1.{u})
    (h13 : SourceStatements.addendum_strengthened_vanishing.{u})
    (h14 : SourceStatements.addendum_converse.{u})
    (h15 : SourceStatements.section_three_foundations.{u})
    (h16 : SourceStatements.mixed_degree_geometry.{u})
    (h17 : SourceStatements.section_three_counterexample)
    (h18 : SourceStatements.lemma_3_1_zero_degree_counterexample)
    (h19 : SourceStatements.translation_operator_foundations.{u})
    (h20 : SourceStatements.translation_geometry_remarks.{u})
    (h21 : SourceStatements.analytic_contact_invariance.{u})
    (h22 : SourceStatements.corollary_counting_estimates.{u})
    (h23 : SourceStatements.section_five_construction.{u})
    (h24 : SourceStatements.masser_wustholz_recovery.{u})
    (h25 : SourceStatements.source_boundary_counterexamples) :
    SourceStatements.theorem_2_1.{u} ∧
    SourceStatements.corollary_2_2.{u} ∧
    SourceStatements.corollary_2_3.{u} ∧
    SourceStatements.lemma_3_1_positive_equation_degrees.{u} ∧
    SourceStatements.lemma_3_2.{u} ∧
    SourceStatements.proposition_3_3.{u} ∧
    SourceStatements.lemma_3_4.{u} ∧
    SourceStatements.proposition_4_3.{u} ∧
    SourceStatements.proposition_4_4.{u} ∧
    SourceStatements.lemma_4_5.{u} ∧
    SourceStatements.lemma_4_6.{u} ∧
    SourceStatements.proposition_4_7.{u} ∧
    SourceStatements.lemma_5_1.{u} ∧
    SourceStatements.addendum_strengthened_vanishing.{u} ∧
    SourceStatements.addendum_converse.{u} ∧
    SourceStatements.section_three_foundations.{u} ∧
    SourceStatements.mixed_degree_geometry.{u} ∧
    SourceStatements.section_three_counterexample ∧
    SourceStatements.lemma_3_1_zero_degree_counterexample ∧
    SourceStatements.translation_operator_foundations.{u} ∧
    SourceStatements.translation_geometry_remarks.{u} ∧
    SourceStatements.analytic_contact_invariance.{u} ∧
    SourceStatements.corollary_counting_estimates.{u} ∧
    SourceStatements.section_five_construction.{u} ∧
    SourceStatements.masser_wustholz_recovery.{u} ∧
    SourceStatements.source_boundary_counterexamples :=
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩

end PhilipponMultiplicity.FullPaperAssembly

open PhilipponMultiplicity
universe u

theorem solution :
    SourceStatements.theorem_2_1.{u} ∧
    SourceStatements.corollary_2_2.{u} ∧
    SourceStatements.corollary_2_3.{u} ∧
    SourceStatements.lemma_3_1_positive_equation_degrees.{u} ∧
    SourceStatements.lemma_3_2.{u} ∧
    SourceStatements.proposition_3_3.{u} ∧
    SourceStatements.lemma_3_4.{u} ∧
    SourceStatements.proposition_4_3.{u} ∧
    SourceStatements.proposition_4_4.{u} ∧
    SourceStatements.lemma_4_5.{u} ∧
    SourceStatements.lemma_4_6.{u} ∧
    SourceStatements.proposition_4_7.{u} ∧
    SourceStatements.lemma_5_1.{u} ∧
    SourceStatements.addendum_strengthened_vanishing.{u} ∧
    SourceStatements.addendum_converse.{u} ∧
    SourceStatements.section_three_foundations.{u} ∧
    SourceStatements.mixed_degree_geometry.{u} ∧
    SourceStatements.section_three_counterexample ∧
    SourceStatements.lemma_3_1_zero_degree_counterexample ∧
    SourceStatements.translation_operator_foundations.{u} ∧
    SourceStatements.translation_geometry_remarks.{u} ∧
    SourceStatements.analytic_contact_invariance.{u} ∧
    SourceStatements.corollary_counting_estimates.{u} ∧
    SourceStatements.section_five_construction.{u} ∧
    SourceStatements.masser_wustholz_recovery.{u} ∧
    SourceStatements.source_boundary_counterexamples := by
  exact FullPaperAssembly.assemble
    (@PhilipponMultiplicity.theorem_2_1)
    (@PhilipponMultiplicity.corollary_2_2)
    (@PhilipponMultiplicity.corollary_2_3)
    (@PhilipponMultiplicity.lemma_3_1_positive_equation_degrees)
    (@PhilipponMultiplicity.lemma_3_2)
    (@PhilipponMultiplicity.proposition_3_3)
    (@PhilipponMultiplicity.lemma_3_4)
    (@PhilipponMultiplicity.proposition_4_3)
    (@PhilipponMultiplicity.proposition_4_4)
    (@PhilipponMultiplicity.lemma_4_5)
    (@PhilipponMultiplicity.lemma_4_6)
    (@PhilipponMultiplicity.proposition_4_7)
    (@PhilipponMultiplicity.lemma_5_1)
    (@PhilipponMultiplicity.addendum_strengthened_vanishing)
    (@PhilipponMultiplicity.addendum_converse)
    (@PhilipponMultiplicity.section_three_foundations)
    (@PhilipponMultiplicity.mixed_degree_geometry)
    (@PhilipponMultiplicity.section_three_counterexample)
    (@PhilipponMultiplicity.lemma_3_1_zero_degree_counterexample)
    (@PhilipponMultiplicity.translation_operator_foundations)
    (@PhilipponMultiplicity.translation_geometry_remarks)
    (@PhilipponMultiplicity.analytic_contact_invariance)
    (@PhilipponMultiplicity.corollary_counting_estimates)
    (@PhilipponMultiplicity.section_five_construction)
    (@PhilipponMultiplicity.masser_wustholz_recovery)
    (@PhilipponMultiplicity.source_boundary_counterexamples)
